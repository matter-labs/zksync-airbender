#pragma once

#include "fold_prologue.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_MAIN_CONT_WINDOW_BOOLEAN_X0 = BWD_MAIN_CONT_WINDOW_DYNAMIC_X0 + 1;
constexpr u32 BWD_MAIN_CONT_WINDOW_BOOLEAN_X1 = 3;

struct bwd_main_cont_triplet {
  e4 value[3];
};

// Adjacent x2 corners occupy one aligned 32-byte sector and can share a load.
template <u32 X0> DEVICE_FORCEINLINE bwd_main_cont_e4_pair bwd_main_cont_resolve_x0_pair(const e4 *corners, const u32 x1, const u32 dynamic_x0) {
  const auto *pairs = reinterpret_cast<const bwd_main_cont_e4_pair *>(corners);
  if constexpr (X0 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X0)
    return load<bwd_main_cont_e4_pair, ld_modifier::ca>(pairs + x1 + 2 * dynamic_x0);
  const u32 x0 = X0 == BWD_MAIN_CONT_WINDOW_DYNAMIC_X0 ? dynamic_x0 : X0;
  if (x0 == 0)
    return load<bwd_main_cont_e4_pair, ld_modifier::ca>(pairs + x1);
  if (x0 == 1)
    return load<bwd_main_cont_e4_pair, ld_modifier::ca>(pairs + x1 + 2);
  const bwd_main_cont_e4_pair zero = load<bwd_main_cont_e4_pair, ld_modifier::ca>(pairs + x1);
  const bwd_main_cont_e4_pair one = load<bwd_main_cont_e4_pair, ld_modifier::ca>(pairs + x1 + 2);
  return bwd_main_cont_e4_pair{{e4::sub(one.value[0], zero.value[0]), e4::sub(one.value[1], zero.value[1])}};
}

// Resolve one semantic SourceId at one `(x1,x0)` selector pair. Published
// corners are in bit order `(x2_low, x1, x0_high)`; the returned triplet is x2 = {0,1,infinity}.
template <u32 X1, u32 X0>
DEVICE_FORCEINLINE bwd_main_cont_triplet bwd_main_cont_resolve_source(const bwd_main_cont_window_desc &desc, const u16 source_id, const u32 row,
                                                                      const u32 dynamic_x0, const u32 dynamic_x1 = 0) {
  static_assert(X1 <= BWD_MAIN_CONT_WINDOW_BOOLEAN_X1, "x1 selector or sentinel is invalid");
  const u32 x1 = X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1 ? dynamic_x1 : X1;
  const u16 lane = desc.source[source_id].publish;
  const e4 *corners = bwd_main_cont_window_column<e4>(desc, lane) + (row << 3);
  bwd_main_cont_e4_pair values;
  if constexpr (X1 < 2 || X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1) {
    values = bwd_main_cont_resolve_x0_pair<X0>(corners, x1, dynamic_x0);
  } else {
    const bwd_main_cont_e4_pair zero = bwd_main_cont_resolve_x0_pair<X0>(corners, 0, dynamic_x0);
    const bwd_main_cont_e4_pair one = bwd_main_cont_resolve_x0_pair<X0>(corners, 1, dynamic_x0);
    values = bwd_main_cont_e4_pair{{e4::sub(one.value[0], zero.value[0]), e4::sub(one.value[1], zero.value[1])}};
  }
  return bwd_main_cont_triplet{{values.value[0], values.value[1], e4::sub(values.value[1], values.value[0])}};
}

// Resolve both product operands through the same selector path. Request both
// operands before interpolation so one source's dependent subtraction does not
// prevent the other source's corner loads from being issued.
struct bwd_main_cont_operand_pairs {
  bwd_main_cont_e4_pair a;
  bwd_main_cont_e4_pair b;
};

DEVICE_FORCEINLINE bwd_main_cont_operand_pairs bwd_main_cont_sub_operand_pairs(const bwd_main_cont_operand_pairs &one,
                                                                               const bwd_main_cont_operand_pairs &zero) {
  return {{{e4::sub(one.a.value[0], zero.a.value[0]), e4::sub(one.a.value[1], zero.a.value[1])}},
          {{e4::sub(one.b.value[0], zero.b.value[0]), e4::sub(one.b.value[1], zero.b.value[1])}}};
}

template <u32 X0>
DEVICE_FORCEINLINE bwd_main_cont_operand_pairs bwd_main_cont_load_operand_pairs(const e4 *a, const e4 *b, const u32 x1, const u32 dynamic_x0) {
  const auto *a_pairs = reinterpret_cast<const bwd_main_cont_e4_pair *>(a);
  const auto *b_pairs = reinterpret_cast<const bwd_main_cont_e4_pair *>(b);
  const u32 x0 = X0 == BWD_MAIN_CONT_WINDOW_DYNAMIC_X0 || X0 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X0 ? dynamic_x0 : X0;
  if (X0 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X0 || x0 < 2)
    return {load<bwd_main_cont_e4_pair, ld_modifier::ca>(a_pairs + x1 + 2 * x0), load<bwd_main_cont_e4_pair, ld_modifier::ca>(b_pairs + x1 + 2 * x0)};
  const bwd_main_cont_operand_pairs zero{load<bwd_main_cont_e4_pair, ld_modifier::ca>(a_pairs + x1),
                                         load<bwd_main_cont_e4_pair, ld_modifier::ca>(b_pairs + x1)};
  const bwd_main_cont_operand_pairs one{load<bwd_main_cont_e4_pair, ld_modifier::ca>(a_pairs + x1 + 2),
                                        load<bwd_main_cont_e4_pair, ld_modifier::ca>(b_pairs + x1 + 2)};
  return bwd_main_cont_sub_operand_pairs(one, zero);
}

template <u32 X1, u32 X0, bool PairSources>
DEVICE_FORCEINLINE void bwd_main_cont_resolve_product_sources(const bwd_main_cont_window_desc &desc, const u16 source_a, const u16 source_b, const u32 row,
                                                              const u32 dynamic_x0, const u32 dynamic_x1, bwd_main_cont_triplet &a, bwd_main_cont_triplet &b) {
  if constexpr (!PairSources) {
    a = bwd_main_cont_resolve_source<X1, X0>(desc, source_a, row, dynamic_x0, dynamic_x1);
    b = bwd_main_cont_resolve_source<X1, X0>(desc, source_b, row, dynamic_x0, dynamic_x1);
  } else {
    const e4 *a_corners = bwd_main_cont_window_column<e4>(desc, desc.source[source_a].publish) + (row << 3);
    const e4 *b_corners = bwd_main_cont_window_column<e4>(desc, desc.source[source_b].publish) + (row << 3);
    bwd_main_cont_operand_pairs values;
    if constexpr (X1 < 2 || X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1) {
      const u32 x1 = X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1 ? dynamic_x1 : X1;
      values = bwd_main_cont_load_operand_pairs<X0>(a_corners, b_corners, x1, dynamic_x0);
    } else {
      const auto zero = bwd_main_cont_load_operand_pairs<X0>(a_corners, b_corners, 0, dynamic_x0);
      const auto one = bwd_main_cont_load_operand_pairs<X0>(a_corners, b_corners, 1, dynamic_x0);
      values = bwd_main_cont_sub_operand_pairs(one, zero);
    }
    a = {{values.a.value[0], values.a.value[1], e4::sub(values.a.value[1], values.a.value[0])}};
    b = {{values.b.value[0], values.b.value[1], e4::sub(values.b.value[1], values.b.value[0])}};
  }
}

DEVICE_FORCEINLINE void bwd_main_cont_add_scaled(const bwd_main_cont_triplet &values, const e4 &coefficient, e4 (&accumulator)[3]) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; x2++)
    accumulator[x2] = e4::fma(coefficient, values.value[x2], accumulator[x2]);
}

DEVICE_FORCEINLINE void bwd_main_cont_add_product(const bwd_main_cont_triplet &lhs, const bwd_main_cont_triplet &rhs, const e4 &coefficient,
                                                  e4 (&accumulator)[3]) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; x2++)
    accumulator[x2] = e4::fma(coefficient, e4::mul(lhs.value[x2], rhs.value[x2]), accumulator[x2]);
}

template <u16 Shape>
DEVICE_FORCEINLINE void bwd_main_cont_apply_immediate(const bwd_main_cont_window_desc &desc, const u16 immediate_id, const bwd_main_cont_triplet &value,
                                                      e4 (&sum)[3]) {
  if (immediate_id == BWD_PROGRAM_IMMEDIATE_ONE) {
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++)
      sum[x2] = e4::add(sum[x2], value.value[x2]);
    return;
  }
  if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_NEGATIVE_GROUP_IMMEDIATE) != 0) {
    if (immediate_id == BWD_PROGRAM_IMMEDIATE_NEG_ONE) {
#pragma unroll
      for (u32 x2 = 0; x2 < 3; x2++)
        sum[x2] = e4::sub(sum[x2], value.value[x2]);
      return;
    }
  }
  if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_BANKED_GROUP_IMMEDIATE) != 0) {
    const bf immediate = bf::from_reduced_raw_repr(desc.immediates[immediate_id - BWD_PROGRAM_IMMEDIATE_RESERVED]);
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++)
      sum[x2] = e4::fma(value.value[x2], immediate, sum[x2]);
  }
}

// Pacing across selector-specialized code paths. The named barrier
// deliberately omits .aligned: selectors execute distinct static instructions.
// All 288 threads visit the same program-word offsets, including group members.
// Barrier 1 is separate from the prologue's block barrier 0.
template <bool Paced> DEVICE_FORCEINLINE void bwd_main_cont_pace(const u32 pc, const u32 program_words) {
  if constexpr (Paced) {
    if (program_words >= 1024 && pc != 0 && pc % 48 == 0)
      asm volatile("barrier.cta.sync 1, 288;" ::: "memory");
  }
}

template <u16 Shape, u32 X1, u32 X0, bool Paced = false, bool PairSources = false>
DEVICE_FORCEINLINE void bwd_main_cont_evaluate(const bwd_main_cont_window_desc &desc, const u32 row, const u32 dynamic_x0, e4 (&accumulator)[3],
                                               const u32 dynamic_x1 = 0) {
  constexpr bool static_x0 = X0 != BWD_MAIN_CONT_WINDOW_DYNAMIC_X0;
  const bool selector_boolean =
      (X1 < 2 || X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1) && (X0 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X0 || (static_x0 ? X0 < 2 : dynamic_x0 < 2));
  if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_C_INIT) != 0) {
    // Absence is tested before the bank read. A universal/superset kernel is
    // therefore byte-inert for a program with no c_init.
    if (selector_boolean && desc.c_init_coeff != BWD_COEFF_NONE) {
      const e4 seed = AB_GKR_BWD_COEFF(static_cast<u16>(desc.c_init_coeff));
      accumulator[0] = seed;
      accumulator[1] = seed;
    }
  }

  for (u32 pc = 0; pc < u32{desc.program_words}; pc += BWD_CONTINUATION_WORDS_PER_TERM) {
    bwd_main_cont_pace<Paced>(pc, desc.program_words);
    const u16 header = desc.program[pc];
    const u16 term_class = (header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
    const u16 coefficient_id = (header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
    const u16 source_a = desc.program[pc + 1];
    const u16 source_b = desc.program[pc + 2];

    if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_GROUPED) != 0) {
      if (term_class == BWD_CONTINUATION_CLASS_GROUP_HEADER) {
        const u16 member_count = source_a;
        e4 group_sum[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
        for (u16 member = 0; member < member_count; member++) {
          pc += BWD_CONTINUATION_WORDS_PER_TERM;
          bwd_main_cont_pace<Paced>(pc, desc.program_words);
          const u16 member_header = desc.program[pc];
          const u16 member_class = (member_header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
          const u16 immediate_id = (member_header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
          if (member_class == BWD_CONTINUATION_CLASS_C0_LINEAR_E4) {
            if (selector_boolean) {
              const bwd_main_cont_triplet a = bwd_main_cont_resolve_source<X1, X0>(desc, desc.program[pc + 1], row, dynamic_x0, dynamic_x1);
              const bwd_main_cont_triplet boolean_a{{a.value[0], a.value[1], e4::ZERO()}};
              bwd_main_cont_apply_immediate<Shape>(desc, immediate_id, boolean_a, group_sum);
            }
          } else if (member_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
            bwd_main_cont_triplet a, b;
            bwd_main_cont_resolve_product_sources<X1, X0, PairSources>(desc, desc.program[pc + 1], desc.program[pc + 2], row, dynamic_x0, dynamic_x1, a, b);
            const bwd_main_cont_triplet product{{e4::mul(a.value[0], b.value[0]), e4::mul(a.value[1], b.value[1]), e4::mul(a.value[2], b.value[2])}};
            bwd_main_cont_apply_immediate<Shape>(desc, immediate_id, product, group_sum);
          }
        }
        const bwd_main_cont_triplet grouped{{group_sum[0], group_sum[1], group_sum[2]}};
        bwd_main_cont_add_scaled(grouped, AB_GKR_BWD_COEFF(coefficient_id), accumulator);
        continue;
      }
    }

    if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_PLAIN_LINEAR) != 0) {
      if (term_class == BWD_CONTINUATION_CLASS_C0_LINEAR_E4) {
        if (selector_boolean) {
          const bwd_main_cont_triplet a = bwd_main_cont_resolve_source<X1, X0>(desc, source_a, row, dynamic_x0, dynamic_x1);
          const bwd_main_cont_triplet boolean_a{{a.value[0], a.value[1], e4::ZERO()}};
          bwd_main_cont_add_scaled(boolean_a, AB_GKR_BWD_COEFF(coefficient_id), accumulator);
        }
        continue;
      }
    }
    if (term_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
      bwd_main_cont_triplet a, b;
      bwd_main_cont_resolve_product_sources<X1, X0, PairSources>(desc, source_a, source_b, row, dynamic_x0, dynamic_x1, a, b);
      bwd_main_cont_add_product(a, b, AB_GKR_BWD_COEFF(coefficient_id), accumulator);
    }
  }
}

DEVICE_FORCEINLINE u32 bwd_main_cont_logical_rows(const gkr_eq_sizes &sizes) { return 1u << (sizes.high[0] + sizes.high[1] + sizes.low); }

DEVICE_FORCEINLINE void bwd_main_cont_window_publish(const bwd_main_cont_window_desc &desc) {
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp_id = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 block_in_tile = blockIdx.x % BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE;
  const u32 publication_partition = block_in_tile / BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;
  const u32 publication_subblock = block_in_tile % BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;
  const u32 publication_row_tile = blockIdx.x / BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE;
  const u32 fold_warp = BWD_MAIN_CONT_WINDOW_BLOCK_WARPS * publication_partition + warp_id;
  const u32 row_in_block = lane / BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;
  const u32 corner_pair = lane % BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;
  const u32 row =
      publication_row_tile * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + publication_subblock * BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK + row_in_block;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  const bool active = row < logical_rows;
  bwd_main_cont_fold_prologue_pair(desc, fold_warp, active ? row : 0, active, corner_pair);
}

template <u16 Shape, u32 X1, u32 X0> DEVICE_FORCEINLINE void bwd_main_cont_window_execute(const bwd_main_cont_window_desc &desc) {
  static_assert((Shape & ~BWD_MAIN_CONT_WINDOW_SHAPE_DEFINED_BITS) == 0, "generated continuation shape has undefined bits");
  const u32 x1 = X1 == BWD_MAIN_CONT_WINDOW_BOOLEAN_X1 ? blockIdx.x % BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS : X1;
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 x0 = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 row_tile = blockIdx.x / BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS;
  const u32 row = row_tile * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + lane;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  const bool active = row < logical_rows;
  const u32 safe_row = active ? row : 0;

  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  if (active) {
    bwd_main_cont_evaluate<Shape, X1, X0>(desc, safe_row, x0, values, x1);
    const e4 eq = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, safe_row);
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++)
      values[x2] = e4::mul(values[x2], eq);
  }

#pragma unroll
  for (u32 x2 = 0; x2 < 3; x2++) {
    const e4 tile = ::airbender::gkr::gkr_trace_holder_partials_warp_reduce_sum<e4>(values[x2]);
    if (lane == 0) {
      // Cell index is 9*x2 + 3*x1 + x0: x2 is the low/first logical axis.
      const u32 cell = 9 * x2 + 3 * x1 + x0;
      store<e4, st_modifier::cs>(desc.partials, tile, row_tile * BWD_MAIN_CONT_WINDOW_TENSOR_CELLS + cell);
    }
  }
}

template <u16 Shape, u32 X1> DEVICE_FORCEINLINE void bwd_main_cont_window_dispatch_x0(const bwd_main_cont_window_desc &desc) {
  if ((threadIdx.x >> BWD_WINDOW_WARP_SHIFT) < 2)
    bwd_main_cont_window_execute<Shape, X1, BWD_MAIN_CONT_WINDOW_BOOLEAN_X0>(desc);
  else
    bwd_main_cont_window_execute<Shape, X1, 2>(desc);
}

#define AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_PUBLICATION_KERNEL(Name)                                                                                            \
  EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS) void Name(                                     \
      const __grid_constant__ airbender::gkr::backward::bwd_main_cont_window_desc desc) {                                                                      \
    if (blockDim.x != airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS ||                                                              \
        gridDim.x != desc.row_tiles * airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE)                                              \
      return;                                                                                                                                                  \
    airbender::gkr::backward::bwd_main_cont_window_publish(desc);                                                                                              \
  }

#define AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL(Name, Shape, MinBlocks)                                                                                      \
  EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_BLOCK_THREADS,                                                            \
                                      MinBlocks) void Name(const __grid_constant__ airbender::gkr::backward::bwd_main_cont_window_desc desc) {                 \
    if (blockDim.x != airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_BLOCK_THREADS ||                                                                          \
        gridDim.x != desc.row_tiles * airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS)                                                          \
      return;                                                                                                                                                  \
    if ((desc.publication_fold != 0 && desc.publication_fold != 3) || desc.source_count > airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_MAX_SOURCES ||        \
        desc.fold_list_offsets[airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_WARPS] != desc.source_count ||                                                   \
        desc.program_words > airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP || desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM != 0)     \
      return;                                                                                                                                                  \
    switch (blockIdx.x % airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS) {                                                                     \
    case 0:                                                                                                                                                    \
      airbender::gkr::backward::bwd_main_cont_window_execute<Shape, 0, airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_DYNAMIC_X0>(desc);                       \
      break;                                                                                                                                                   \
    case 1:                                                                                                                                                    \
      airbender::gkr::backward::bwd_main_cont_window_execute<Shape, 1, airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_DYNAMIC_X0>(desc);                       \
      break;                                                                                                                                                   \
    case 2:                                                                                                                                                    \
      airbender::gkr::backward::bwd_main_cont_window_execute<Shape, 2, airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_DYNAMIC_X0>(desc);                       \
      break;                                                                                                                                                   \
    }                                                                                                                                                          \
  }

#define AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL(Name, Shape, MinBlocks)                                                                                  \
  EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_BLOCK_THREADS,                                                            \
                                      MinBlocks) void Name(const __grid_constant__ airbender::gkr::backward::bwd_main_cont_window_desc desc) {                 \
    if (blockDim.x != airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_BLOCK_THREADS ||                                                                          \
        gridDim.x != desc.row_tiles * airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS)                                                          \
      return;                                                                                                                                                  \
    if ((desc.publication_fold != 0 && desc.publication_fold != 3) || desc.source_count > airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_MAX_SOURCES ||        \
        desc.fold_list_offsets[airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_WARPS] != desc.source_count ||                                                   \
        desc.program_words > airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP || desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM != 0)     \
      return;                                                                                                                                                  \
    if (blockIdx.x % airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS < 2)                                                                       \
      airbender::gkr::backward::bwd_main_cont_window_dispatch_x0<Shape, airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_BOOLEAN_X1>(desc);                      \
    else                                                                                                                                                       \
      airbender::gkr::backward::bwd_main_cont_window_dispatch_x0<Shape, 2>(desc);                                                                              \
  }

} // namespace airbender::gkr::backward
