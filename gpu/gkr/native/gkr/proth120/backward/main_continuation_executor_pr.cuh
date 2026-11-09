#pragma once

#include "../../support/eq_inline.cuh"
#include "../../support/kernel_helpers.cuh"
#include "fold_prologue_pr.cuh"

namespace airbender::gkr::proth120::backward {

constexpr u32 BWD_PR_MAIN_CONT_DYNAMIC_X0 = 3;
constexpr u32 BWD_PR_MAIN_CONT_BOOLEAN_X0 = BWD_PR_MAIN_CONT_DYNAMIC_X0 + 1;
constexpr u32 BWD_PR_MAIN_CONT_BOOLEAN_X1 = 3;

constexpr u16 BWD_PR_MAIN_CONT_SHAPE_PLAIN_LINEAR = 1u << 0;
constexpr u16 BWD_PR_MAIN_CONT_SHAPE_GROUPED = 1u << 1;
constexpr u16 BWD_PR_MAIN_CONT_SHAPE_C_INIT = 1u << 2;
constexpr u16 BWD_PR_MAIN_CONT_SHAPE_BANKED_GROUP_IMMEDIATE = 1u << 3;
constexpr u16 BWD_PR_MAIN_CONT_SHAPE_NEGATIVE_GROUP_IMMEDIATE = 1u << 4;
constexpr u16 BWD_PR_MAIN_CONT_SHAPE_DEFINED_BITS = 0x1f;

struct bwd_pr_main_cont_triplet {
  pr value[3];
};

template <u32 X0> DEVICE_FORCEINLINE bwd_pr_pair bwd_pr_main_cont_resolve_x0_pair(const pr *corners, const u32 x1, const u32 dynamic_x0) {
  const auto *pairs = reinterpret_cast<const bwd_pr_pair *>(corners);
  if constexpr (X0 == BWD_PR_MAIN_CONT_BOOLEAN_X0)
    return load<bwd_pr_pair, ld_modifier::ca>(pairs + x1 + 2 * dynamic_x0);
  const u32 x0 = X0 == BWD_PR_MAIN_CONT_DYNAMIC_X0 ? dynamic_x0 : X0;
  if (x0 == 0)
    return load<bwd_pr_pair, ld_modifier::ca>(pairs + x1);
  if (x0 == 1)
    return load<bwd_pr_pair, ld_modifier::ca>(pairs + x1 + 2);
  const bwd_pr_pair zero = load<bwd_pr_pair, ld_modifier::ca>(pairs + x1);
  const bwd_pr_pair one = load<bwd_pr_pair, ld_modifier::ca>(pairs + x1 + 2);
  return bwd_pr_pair{{pr::sub(one.value[0], zero.value[0]), pr::sub(one.value[1], zero.value[1])}};
}

template <u32 X1, u32 X0>
DEVICE_FORCEINLINE bwd_pr_main_cont_triplet bwd_pr_main_cont_resolve_source(const bwd_pr_main_cont_desc &desc, const u16 source_id, const u32 row,
                                                                            const u32 dynamic_x0, const u32 dynamic_x1) {
  static_assert(X1 <= BWD_PR_MAIN_CONT_BOOLEAN_X1, "x1 selector or sentinel is invalid");
  const u32 x1 = X1 == BWD_PR_MAIN_CONT_BOOLEAN_X1 ? dynamic_x1 : X1;
  const pr *corners = bwd_pr_main_cont_column(desc, desc.source[source_id].publish) + (row << 3);
  bwd_pr_pair values;
  if constexpr (X1 < 2 || X1 == BWD_PR_MAIN_CONT_BOOLEAN_X1) {
    values = bwd_pr_main_cont_resolve_x0_pair<X0>(corners, x1, dynamic_x0);
  } else {
    const bwd_pr_pair zero = bwd_pr_main_cont_resolve_x0_pair<X0>(corners, 0, dynamic_x0);
    const bwd_pr_pair one = bwd_pr_main_cont_resolve_x0_pair<X0>(corners, 1, dynamic_x0);
    values = bwd_pr_pair{{pr::sub(one.value[0], zero.value[0]), pr::sub(one.value[1], zero.value[1])}};
  }
  return bwd_pr_main_cont_triplet{{values.value[0], values.value[1], pr::sub(values.value[1], values.value[0])}};
}

DEVICE_FORCEINLINE void bwd_pr_main_cont_add_scaled(const bwd_pr_main_cont_triplet &values, const pr &coefficient, pr (&accumulator)[3]) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; x2++)
    accumulator[x2] = pr::fma(coefficient, values.value[x2], accumulator[x2]);
}

DEVICE_FORCEINLINE void bwd_pr_main_cont_add_product(const bwd_pr_main_cont_triplet &lhs, const bwd_pr_main_cont_triplet &rhs, const pr &coefficient,
                                                     pr (&accumulator)[3]) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; x2++)
    accumulator[x2] = pr::fma(coefficient, pr::mul(lhs.value[x2], rhs.value[x2]), accumulator[x2]);
}

template <u16 Shape>
DEVICE_FORCEINLINE void bwd_pr_main_cont_apply_immediate(const bwd_pr_main_cont_desc &desc, const u16 immediate_id, const bwd_pr_main_cont_triplet &value,
                                                         pr (&sum)[3]) {
  if (immediate_id == BWD_PROGRAM_IMMEDIATE_ONE) {
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++)
      sum[x2] = pr::add(sum[x2], value.value[x2]);
    return;
  }
  if constexpr ((Shape & BWD_PR_MAIN_CONT_SHAPE_NEGATIVE_GROUP_IMMEDIATE) != 0) {
    if (immediate_id == BWD_PROGRAM_IMMEDIATE_NEG_ONE) {
#pragma unroll
      for (u32 x2 = 0; x2 < 3; x2++)
        sum[x2] = pr::sub(sum[x2], value.value[x2]);
      return;
    }
  }
  if constexpr ((Shape & BWD_PR_MAIN_CONT_SHAPE_BANKED_GROUP_IMMEDIATE) != 0) {
    const pr immediate = load<pr, ld_modifier::ca>(desc.immediates, immediate_id - BWD_PROGRAM_IMMEDIATE_RESERVED);
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++)
      sum[x2] = pr::fma(value.value[x2], immediate, sum[x2]);
  }
}

DEVICE_FORCEINLINE pr bwd_pr_main_cont_coefficient(const bwd_pr_main_cont_desc &desc, const u32 coefficient_id) {
  return load<pr, ld_modifier::ca>(desc.coefficients, coefficient_id);
}

template <u16 Shape, u32 X1, u32 X0>
DEVICE_FORCEINLINE void bwd_pr_main_cont_evaluate(const bwd_pr_main_cont_desc &desc, const u32 row, const u32 dynamic_x0, pr (&accumulator)[3],
                                                  const u32 dynamic_x1) {
  constexpr bool static_x0 = X0 != BWD_PR_MAIN_CONT_DYNAMIC_X0;
  const bool selector_boolean = (X1 < 2 || X1 == BWD_PR_MAIN_CONT_BOOLEAN_X1) && (X0 == BWD_PR_MAIN_CONT_BOOLEAN_X0 || (static_x0 ? X0 < 2 : dynamic_x0 < 2));
  if constexpr ((Shape & BWD_PR_MAIN_CONT_SHAPE_C_INIT) != 0) {
    if (selector_boolean && desc.c_init_coeff != BWD_COEFF_NONE) {
      const pr seed = bwd_pr_main_cont_coefficient(desc, desc.c_init_coeff);
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

    if constexpr ((Shape & BWD_PR_MAIN_CONT_SHAPE_GROUPED) != 0) {
      if (term_class == BWD_CONTINUATION_CLASS_GROUP_HEADER) {
        const u16 member_count = source_a;
        pr group_sum[3]{pr::ZERO(), pr::ZERO(), pr::ZERO()};
        for (u16 member = 0; member < member_count; member++) {
          pc += BWD_CONTINUATION_WORDS_PER_TERM;
          const u16 member_header = desc.program[pc];
          const u16 member_class = (member_header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
          const u16 immediate_id = (member_header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
          if (member_class == BWD_CONTINUATION_CLASS_C0_LINEAR_E4) {
            if (selector_boolean) {
              const bwd_pr_main_cont_triplet a = bwd_pr_main_cont_resolve_source<X1, X0>(desc, desc.program[pc + 1], row, dynamic_x0, dynamic_x1);
              const bwd_pr_main_cont_triplet boolean_a{{a.value[0], a.value[1], pr::ZERO()}};
              bwd_pr_main_cont_apply_immediate<Shape>(desc, immediate_id, boolean_a, group_sum);
            }
          } else if (member_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
            const bwd_pr_main_cont_triplet a = bwd_pr_main_cont_resolve_source<X1, X0>(desc, desc.program[pc + 1], row, dynamic_x0, dynamic_x1);
            const bwd_pr_main_cont_triplet b = bwd_pr_main_cont_resolve_source<X1, X0>(desc, desc.program[pc + 2], row, dynamic_x0, dynamic_x1);
            const bwd_pr_main_cont_triplet product{{pr::mul(a.value[0], b.value[0]), pr::mul(a.value[1], b.value[1]), pr::mul(a.value[2], b.value[2])}};
            bwd_pr_main_cont_apply_immediate<Shape>(desc, immediate_id, product, group_sum);
          }
        }
        const bwd_pr_main_cont_triplet grouped{{group_sum[0], group_sum[1], group_sum[2]}};
        bwd_pr_main_cont_add_scaled(grouped, bwd_pr_main_cont_coefficient(desc, coefficient_id), accumulator);
        continue;
      }
    }

    if constexpr ((Shape & BWD_PR_MAIN_CONT_SHAPE_PLAIN_LINEAR) != 0) {
      if (term_class == BWD_CONTINUATION_CLASS_C0_LINEAR_E4) {
        if (selector_boolean) {
          const bwd_pr_main_cont_triplet a = bwd_pr_main_cont_resolve_source<X1, X0>(desc, source_a, row, dynamic_x0, dynamic_x1);
          const bwd_pr_main_cont_triplet boolean_a{{a.value[0], a.value[1], pr::ZERO()}};
          bwd_pr_main_cont_add_scaled(boolean_a, bwd_pr_main_cont_coefficient(desc, coefficient_id), accumulator);
        }
        continue;
      }
    }
    if (term_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
      const bwd_pr_main_cont_triplet a = bwd_pr_main_cont_resolve_source<X1, X0>(desc, source_a, row, dynamic_x0, dynamic_x1);
      const bwd_pr_main_cont_triplet b = bwd_pr_main_cont_resolve_source<X1, X0>(desc, source_b, row, dynamic_x0, dynamic_x1);
      bwd_pr_main_cont_add_product(a, b, bwd_pr_main_cont_coefficient(desc, coefficient_id), accumulator);
    }
  }
}

template <u16 Shape> DEVICE_FORCEINLINE void bwd_pr_main_cont_execute(const bwd_pr_main_cont_desc &desc, pr (&weights)[BWD_PR_MAIN_CONT_FOLD_WEIGHTS]) {
  static_assert((Shape & ~BWD_PR_MAIN_CONT_SHAPE_DEFINED_BITS) == 0, "generated continuation shape has undefined bits");
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 logical_rows = bwd_pr_main_cont_logical_rows(desc.eq_sizes);
  if (threadIdx.x < BWD_PR_MAIN_CONT_FOLD_WEIGHTS)
    weights[threadIdx.x] = load<pr, ld_modifier::ca>(desc.fold_weights, BWD_FOLD_WEIGHT_BASE_D3 + threadIdx.x);
  __syncthreads();
  for (u32 subrow = 0; subrow < BWD_PR_MAIN_CONT_SUBROWS; subrow++) {
    const u32 row = blockIdx.x * BWD_PR_MAIN_CONT_ROWS_PER_TILE + subrow * BWD_PR_MAIN_CONT_ROWS_PER_PASS + lane / BWD_PR_MAIN_CONT_LANES_PER_ROW;
    if (row < logical_rows)
      bwd_pr_main_cont_fold_prologue(desc, warp, row, lane % BWD_PR_MAIN_CONT_LANES_PER_ROW, weights);
  }
  __syncthreads();

  const u32 row = blockIdx.x * BWD_PR_MAIN_CONT_ROWS_PER_TILE + lane;
  const bool active = row < logical_rows;
  const pr eq = gkr_compute_eq_inline_global<pr>(desc.eq_high, desc.eq_high + GKR_EQ_GROUP_TABLE_LEN, desc.eq_low, desc.eq_sizes, active ? row : 0);
#pragma unroll 1
  for (u32 x1 = 0; x1 < 3; x1++) {
    pr values[3]{pr::ZERO(), pr::ZERO(), pr::ZERO()};
    if (active) {
      if (x1 < 2)
        bwd_pr_main_cont_evaluate<Shape, BWD_PR_MAIN_CONT_BOOLEAN_X1, BWD_PR_MAIN_CONT_DYNAMIC_X0>(desc, row, warp, values, x1);
      else
        bwd_pr_main_cont_evaluate<Shape, 2, BWD_PR_MAIN_CONT_DYNAMIC_X0>(desc, row, warp, values, 0);
#pragma unroll
      for (u32 x2 = 0; x2 < 3; x2++)
        values[x2] = pr::mul(values[x2], eq);
    }
#pragma unroll
    for (u32 x2 = 0; x2 < 3; x2++) {
      const pr tile = gkr_trace_holder_partials_warp_reduce_sum<pr>(values[x2]);
      if (lane == 0)
        store<pr, st_modifier::cs>(desc.partials, tile, blockIdx.x * BWD_PR_MAIN_CONT_TENSOR_CELLS + 9 * x2 + 3 * x1 + warp);
    }
  }
}

DEVICE_FORCEINLINE bool bwd_pr_main_cont_valid(const bwd_pr_main_cont_desc &desc) {
  return blockDim.x == BWD_PR_MAIN_CONT_BLOCK_THREADS && gridDim.x == desc.row_tiles && desc.row_tiles != 0 &&
         desc.source_count <= BWD_PR_MAIN_CONT_MAX_SOURCES && desc.fold_list_offsets[BWD_PR_MAIN_CONT_FOLD_LISTS] == desc.source_count &&
         desc.program_words <= BWD_PR_MAIN_CONT_PROGRAM_WORD_CAP && desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM == 0;
}

#define AB_PR_GKR_BWD_MAIN_CONT_DEFINE_KERNEL(Name, Mask, MinBlocks)                                                                                           \
  EXTERN __global__ __launch_bounds__(::airbender::gkr::proth120::backward::BWD_PR_MAIN_CONT_BLOCK_THREADS,                                                    \
                                      MinBlocks) void Name(const __grid_constant__ ::airbender::gkr::proth120::backward::bwd_pr_main_cont_desc desc) {         \
    __shared__ ::airbender::primitives::field::proth120 fold_weights[::airbender::gkr::proth120::backward::BWD_PR_MAIN_CONT_FOLD_WEIGHTS];                     \
    if (!::airbender::gkr::proth120::backward::bwd_pr_main_cont_valid(desc))                                                                                   \
      return;                                                                                                                                                  \
    ::airbender::gkr::proth120::backward::bwd_pr_main_cont_execute<(Mask)>(desc, fold_weights);                                                                \
  }

} // namespace airbender::gkr::proth120::backward
