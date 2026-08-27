#pragma once

#include "fold_prologue.cuh"

namespace airbender::gkr::backward {

struct bwd_main_cont_triplet {
  e4 value[3];
};

template <u32 X0> DEVICE_FORCEINLINE e4 bwd_main_cont_resolve_x0(const e4 *corners, const u32 x2, const u32 x1, const u32 dynamic_x0) {
  static_assert(X0 <= BWD_MAIN_CONT_WINDOW_DYNAMIC_X0, "x0 selector or sentinel is invalid");
  const u32 base = x2 + 2 * x1;
  const u32 x0 = X0 == BWD_MAIN_CONT_WINDOW_DYNAMIC_X0 ? dynamic_x0 : X0;
  if constexpr (X0 == 0)
    return load<e4, ld_modifier::ca>(corners, base);
  if constexpr (X0 == 1)
    return load<e4, ld_modifier::ca>(corners, base + 4);
  if constexpr (X0 == 2)
    return e4::sub(load<e4, ld_modifier::ca>(corners, base + 4), load<e4, ld_modifier::ca>(corners, base));
  if (x0 == 0)
    return load<e4, ld_modifier::ca>(corners, base);
  if (x0 == 1)
    return load<e4, ld_modifier::ca>(corners, base + 4);
  return e4::sub(load<e4, ld_modifier::ca>(corners, base + 4), load<e4, ld_modifier::ca>(corners, base));
}

// Resolve one semantic SourceId at one `(x1,x0)` selector pair. Published
// corners are in bit order `(x2_low, x1, x0_high)`, while the returned triplet
// is x2 = {0,1,infinity}. This makes the landed low/first x2 axis stride nine.
template <u32 X1, u32 X0>
DEVICE_FORCEINLINE bwd_main_cont_triplet bwd_main_cont_resolve_source(const bwd_main_cont_window_desc &desc, const u16 source_id, const u32 row,
                                                                      const u32 dynamic_x0) {
  static_assert(X1 < 3, "x1 selector is ternary");
  const u16 lane = desc.source[source_id].publish;
  const e4 *corners = bwd_main_cont_window_column<e4>(desc, lane) + (row << 3);
  e4 x2_values[2];
#pragma unroll
  for (u32 x2 = 0; x2 < 2; x2++) {
    if constexpr (X1 < 2) {
      x2_values[x2] = bwd_main_cont_resolve_x0<X0>(corners, x2, X1, dynamic_x0);
    } else {
      const e4 x1_zero = bwd_main_cont_resolve_x0<X0>(corners, x2, 0, dynamic_x0);
      const e4 x1_one = bwd_main_cont_resolve_x0<X0>(corners, x2, 1, dynamic_x0);
      x2_values[x2] = e4::sub(x1_one, x1_zero);
    }
  }
  return bwd_main_cont_triplet{{x2_values[0], x2_values[1], e4::sub(x2_values[1], x2_values[0])}};
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

template <u16 Shape, u32 X1, u32 X0>
DEVICE_FORCEINLINE void bwd_main_cont_evaluate(const bwd_main_cont_window_desc &desc, const u32 row, const u32 dynamic_x0, e4 (&accumulator)[3]) {
  constexpr bool static_x0 = X0 != BWD_MAIN_CONT_WINDOW_DYNAMIC_X0;
  const bool selector_boolean = X1 < 2 && (static_x0 ? X0 < 2 : dynamic_x0 < 2);
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
          const u16 member_header = desc.program[pc];
          const u16 member_class = (member_header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
          const u16 immediate_id = (member_header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
          if (member_class == BWD_CONTINUATION_CLASS_C0_LINEAR_E4) {
            if (selector_boolean) {
              const bwd_main_cont_triplet a = bwd_main_cont_resolve_source<X1, X0>(desc, desc.program[pc + 1], row, dynamic_x0);
              const bwd_main_cont_triplet boolean_a{{a.value[0], a.value[1], e4::ZERO()}};
              bwd_main_cont_apply_immediate<Shape>(desc, immediate_id, boolean_a, group_sum);
            }
          } else if (member_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
            const bwd_main_cont_triplet a = bwd_main_cont_resolve_source<X1, X0>(desc, desc.program[pc + 1], row, dynamic_x0);
            const bwd_main_cont_triplet b = bwd_main_cont_resolve_source<X1, X0>(desc, desc.program[pc + 2], row, dynamic_x0);
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
          const bwd_main_cont_triplet a = bwd_main_cont_resolve_source<X1, X0>(desc, source_a, row, dynamic_x0);
          const bwd_main_cont_triplet boolean_a{{a.value[0], a.value[1], e4::ZERO()}};
          bwd_main_cont_add_scaled(boolean_a, AB_GKR_BWD_COEFF(coefficient_id), accumulator);
        }
        continue;
      }
    }
    if (term_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
      const bwd_main_cont_triplet a = bwd_main_cont_resolve_source<X1, X0>(desc, source_a, row, dynamic_x0);
      const bwd_main_cont_triplet b = bwd_main_cont_resolve_source<X1, X0>(desc, source_b, row, dynamic_x0);
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
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 x0 = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 row_tile = blockIdx.x / BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS;
  const u32 row = row_tile * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + lane;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  const bool active = row < logical_rows;
  const u32 safe_row = active ? row : 0;

  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  if (active) {
    bwd_main_cont_evaluate<Shape, X1, X0>(desc, safe_row, x0, values);
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
      const u32 cell = 9 * x2 + 3 * X1 + x0;
      store<e4, st_modifier::cs>(desc.partials, tile, row_tile * BWD_MAIN_CONT_WINDOW_TENSOR_CELLS + cell);
    }
  }
}

template <u16 Shape, u32 X1> DEVICE_FORCEINLINE void bwd_main_cont_window_dispatch_x0(const bwd_main_cont_window_desc &desc) {
  switch (threadIdx.x >> BWD_WINDOW_WARP_SHIFT) {
  case 0:
    bwd_main_cont_window_execute<Shape, X1, 0>(desc);
    break;
  case 1:
    bwd_main_cont_window_execute<Shape, X1, 1>(desc);
    break;
  case 2:
    bwd_main_cont_window_execute<Shape, X1, 2>(desc);
    break;
  }
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
    switch (blockIdx.x % airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS) {                                                                     \
    case 0:                                                                                                                                                    \
      airbender::gkr::backward::bwd_main_cont_window_dispatch_x0<Shape, 0>(desc);                                                                              \
      break;                                                                                                                                                   \
    case 1:                                                                                                                                                    \
      airbender::gkr::backward::bwd_main_cont_window_dispatch_x0<Shape, 1>(desc);                                                                              \
      break;                                                                                                                                                   \
    case 2:                                                                                                                                                    \
      airbender::gkr::backward::bwd_main_cont_window_dispatch_x0<Shape, 2>(desc);                                                                              \
      break;                                                                                                                                                   \
    }                                                                                                                                                          \
  }

} // namespace airbender::gkr::backward
