#pragma once

#include "fold_prologue.cuh"

namespace airbender::gkr::backward {

struct bwd_main_cont_triplet {
  e4 value[3];
};

DEVICE_FORCEINLINE e4 bwd_main_cont_select(const e4 &zero, const e4 &one, const u32 selector) {
  return selector == 0 ? zero : selector == 1 ? one : e4::sub(one, zero);
}

// Resolve one semantic SourceId at one `(x1,x0)` selector pair. Published
// corners are in bit order `(x2_low, x1, x0_high)`, while the returned triplet
// is x2 = {0,1,infinity}. This makes the landed low/first x2 axis stride nine.
DEVICE_FORCEINLINE bwd_main_cont_triplet bwd_main_cont_resolve_source(const bwd_main_cont_window_desc &desc, const u16 source_id, const u32 row,
                                                                      const u32 selector_pair) {
  const u16 lane = desc.source[source_id].publish;
  const e4 *corners = bwd_main_cont_window_column<e4>(desc, lane) + (row << 3);
  const u32 x1 = selector_pair / 3;
  const u32 x0 = selector_pair - 3 * x1;
  e4 x2_values[2];
#pragma unroll
  for (u32 x2 = 0; x2 < 2; x2++) {
    const e4 x1_zero = bwd_main_cont_select(load<e4, ld_modifier::ca>(corners, x2), load<e4, ld_modifier::ca>(corners, x2 + 4), x0);
    const e4 x1_one = bwd_main_cont_select(load<e4, ld_modifier::ca>(corners, x2 + 2), load<e4, ld_modifier::ca>(corners, x2 + 6), x0);
    x2_values[x2] = bwd_main_cont_select(x1_zero, x1_one, x1);
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
  if (immediate_id == BWD_SEG_IMMEDIATE_ONE) {
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++)
      sum[x2] = e4::add(sum[x2], value.value[x2]);
    return;
  }
  if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_NEGATIVE_GROUP_IMMEDIATE) != 0) {
    if (immediate_id == BWD_SEG_IMMEDIATE_NEG_ONE) {
#pragma unroll
      for (u32 x2 = 0; x2 < 3; x2++)
        sum[x2] = e4::sub(sum[x2], value.value[x2]);
      return;
    }
  }
  if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_BANKED_GROUP_IMMEDIATE) != 0) {
    const bf immediate = bf::from_reduced_raw_repr(desc.immediates[immediate_id - BWD_SEG_IMMEDIATE_RESERVED]);
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++)
      sum[x2] = e4::fma(value.value[x2], immediate, sum[x2]);
  }
}

template <u16 Shape>
DEVICE_FORCEINLINE void bwd_main_cont_evaluate(const bwd_main_cont_window_desc &desc, const u32 row, const u32 selector_pair, e4 (&accumulator)[3]) {
  const bool selector_boolean = selector_pair / 3 < 2 && selector_pair % 3 < 2;
  if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_C_INIT) != 0) {
    // Absence is tested before the bank read. A universal/superset kernel is
    // therefore byte-inert for a program with no c_init.
    if (selector_boolean && desc.c_init_coeff != BWD_SEG_C_INIT_NONE) {
      const e4 seed = AB_GKR_BWD_SEG_COEFF(static_cast<u16>(desc.c_init_coeff));
      accumulator[0] = seed;
      accumulator[1] = seed;
    }
  }

  for (u32 pc = 0; pc < u32{desc.program_words}; pc += BWD_SEG_WORDS_PER_TERM) {
    const u16 header = desc.program[pc];
    const u16 term_class = (header >> BWD_SEG_CLASS_SHIFT) & BWD_SEG_CLASS_MASK;
    const u16 coefficient_id = (header >> BWD_SEG_COEFFICIENT_SHIFT) & BWD_SEG_COEFFICIENT_MASK;
    const u16 source_a = desc.program[pc + 1];
    const u16 source_b = desc.program[pc + 2];

    if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_GROUPED) != 0) {
      if (term_class == BWD_SEG_EXT_CLASS_GROUP_HEADER) {
        const u16 member_count = source_a;
        e4 group_sum[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
        for (u16 member = 0; member < member_count; member++) {
          pc += BWD_SEG_WORDS_PER_TERM;
          const u16 member_header = desc.program[pc];
          const u16 member_class = (member_header >> BWD_SEG_CLASS_SHIFT) & BWD_SEG_CLASS_MASK;
          const u16 immediate_id = (member_header >> BWD_SEG_COEFFICIENT_SHIFT) & BWD_SEG_COEFFICIENT_MASK;
          const bwd_main_cont_triplet a = bwd_main_cont_resolve_source(desc, desc.program[pc + 1], row, selector_pair);
          if (member_class == BWD_SEG_EXT_CLASS_C0_LINEAR_E4) {
            if (selector_boolean) {
              const bwd_main_cont_triplet boolean_a{{a.value[0], a.value[1], e4::ZERO()}};
              bwd_main_cont_apply_immediate<Shape>(desc, immediate_id, boolean_a, group_sum);
            }
          } else if (member_class == BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4) {
            const bwd_main_cont_triplet b = bwd_main_cont_resolve_source(desc, desc.program[pc + 2], row, selector_pair);
            const bwd_main_cont_triplet product{{e4::mul(a.value[0], b.value[0]), e4::mul(a.value[1], b.value[1]), e4::mul(a.value[2], b.value[2])}};
            bwd_main_cont_apply_immediate<Shape>(desc, immediate_id, product, group_sum);
          }
        }
        const bwd_main_cont_triplet grouped{{group_sum[0], group_sum[1], group_sum[2]}};
        bwd_main_cont_add_scaled(grouped, AB_GKR_BWD_SEG_COEFF(coefficient_id), accumulator);
        continue;
      }
    }

    if constexpr ((Shape & BWD_MAIN_CONT_WINDOW_SHAPE_PLAIN_LINEAR) != 0) {
      if (term_class == BWD_SEG_EXT_CLASS_C0_LINEAR_E4) {
        if (selector_boolean) {
          const bwd_main_cont_triplet a = bwd_main_cont_resolve_source(desc, source_a, row, selector_pair);
          const bwd_main_cont_triplet boolean_a{{a.value[0], a.value[1], e4::ZERO()}};
          bwd_main_cont_add_scaled(boolean_a, AB_GKR_BWD_SEG_COEFF(coefficient_id), accumulator);
        }
        continue;
      }
    }
    if (term_class == BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4) {
      const bwd_main_cont_triplet a = bwd_main_cont_resolve_source(desc, source_a, row, selector_pair);
      const bwd_main_cont_triplet b = bwd_main_cont_resolve_source(desc, source_b, row, selector_pair);
      bwd_main_cont_add_product(a, b, AB_GKR_BWD_SEG_COEFF(coefficient_id), accumulator);
    }
  }
}

DEVICE_FORCEINLINE u32 bwd_main_cont_logical_rows(const gkr_eq_sizes &sizes) { return 1u << (sizes.high[0] + sizes.high[1] + sizes.low); }

template <u16 Shape> DEVICE_FORCEINLINE void bwd_main_cont_window_execute(const bwd_main_cont_window_desc &desc) {
  static_assert((Shape & ~BWD_MAIN_CONT_WINDOW_SHAPE_DEFINED_BITS) == 0, "generated continuation shape has undefined bits");
  const u32 lane = threadIdx.x & BWD_SEG_LANE_INDEX_MASK;
  const u32 warp_id = threadIdx.x >> BWD_SEG_WARP_SHIFT;
  const u32 row = blockIdx.x * BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE + lane;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  const bool active = row < logical_rows;
  const u32 safe_row = active ? row : 0;

  bwd_main_cont_fold_prologue(desc, warp_id, safe_row, active);
  __syncthreads();

  e4 values[3]{e4::ZERO(), e4::ZERO(), e4::ZERO()};
  if (active) {
    bwd_main_cont_evaluate<Shape>(desc, safe_row, warp_id, values);
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
      const u32 cell = 9 * x2 + warp_id;
      store<e4, st_modifier::cs>(desc.partials, tile, blockIdx.x * BWD_MAIN_CONT_WINDOW_TENSOR_CELLS + cell);
    }
  }
}

#define AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL(Name, Shape, MinBlocks)                                                                                      \
  EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_BLOCK_THREADS,                                                            \
                                      MinBlocks) void Name(const __grid_constant__ airbender::gkr::backward::bwd_main_cont_window_desc desc) {                 \
    if (blockDim.x != airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_BLOCK_THREADS || gridDim.x != desc.row_tiles)                                             \
      return;                                                                                                                                                  \
    if ((desc.publication_fold != 0 && desc.publication_fold != 3) || desc.source_count > airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_MAX_SOURCES ||        \
        desc.fold_list_offsets[airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_WARPS] != desc.source_count ||                                                   \
        desc.program_words > airbender::gkr::backward::BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP || desc.program_words % BWD_SEG_WORDS_PER_TERM != 0)              \
      return;                                                                                                                                                  \
    airbender::gkr::backward::bwd_main_cont_window_execute<Shape>(desc);                                                                                       \
  }

} // namespace airbender::gkr::backward
