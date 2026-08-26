#pragma once

#include <type_traits>

#include "../../support/lookup_helpers.cuh"
#include "../window/window_geometry.cuh"

namespace airbender::gkr::backward {

constexpr u16 DR_CONTINUATION_FIRST_ACCESS_BIT = 0x8000u;
constexpr u32 DR_WINDOW_CONT_OCCURRENCES = GKR_DIM_REDUCING_SLOTS * GKR_DIM_REDUCING_INPUTS_PER_SLOT;
constexpr u32 DR_WINDOW_CONT_PAIRS_PER_TILE = BWD_WINDOW_ROWS_PER_TILE * 8u;

struct alignas(16) gkr_dr_cont_window3_desc {
  gkr_dim_reducing_batch<e4> batch;
  const e4 *eq_high_0;
  const e4 *eq_high_1;
  e4 *partials;
  const e4 *claim_point;
  u32 log_rows;
  u32 start_round;
  u32 reserved[2];
};

static_assert(sizeof(gkr_dr_cont_window3_desc) == 384, "gkr_dr_cont_window3_desc/DrWindowContinuationLaunchBinding ABI size drift");
static_assert(alignof(gkr_dr_cont_window3_desc) == 16, "gkr_dr_cont_window3_desc ABI alignment drift");
static_assert(sizeof(gkr_dr_cont_window3_desc) <= BWD_WINDOW_DESC_CAP, "gkr_dr_cont_window3_desc exceeds the CUDA kernel-argument ceiling");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, batch) == 0, "DR continuation batch ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, eq_high_0) == 336, "DR continuation eq_high_0 ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, eq_high_1) == 344, "DR continuation eq_high_1 ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, partials) == 352, "DR continuation partials ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, claim_point) == 360, "DR continuation claim_point ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, log_rows) == 368, "DR continuation log_rows ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, start_round) == 372, "DR continuation start_round ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_cont_window3_desc, reserved) == 376, "DR continuation reserved ABI offset drift");
static_assert(std::is_standard_layout_v<gkr_dr_cont_window3_desc>, "DR continuation descriptor must be standard-layout");
static_assert(std::is_trivially_copyable_v<gkr_dr_cont_window3_desc>, "DR continuation descriptor must be trivially copyable");
static_assert(GKR_DIM_REDUCING_INPUTS_PER_SLOT == GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, "DR input and batch-challenge cardinalities must match");

struct alignas(32) dr_window_e4_pair {
  e4 value[2];
};

static_assert(sizeof(dr_window_e4_pair) == 32 && alignof(dr_window_e4_pair) == 32, "DR continuation pair must be one aligned 256-bit transaction");

DEVICE_FORCEINLINE dr_window_e4_pair dr_window_load_e4_pair_guarded(const e4 *source, const size_t pair_index, const bool active) {
  if (!active)
    return {{e4::ZERO(), e4::ZERO()}};
  return load<dr_window_e4_pair, ld_modifier::cs>(reinterpret_cast<const dr_window_e4_pair *>(source) + pair_index);
}

DEVICE_FORCEINLINE dr_window_e4_pair dr_window_pair_fold(const dr_window_e4_pair zero, const dr_window_e4_pair one, const e4 challenge) {
  dr_window_e4_pair result;
#pragma unroll
  for (u32 gate_bit = 0; gate_bit < 2; ++gate_bit)
    result.value[gate_bit] = e4::fma(challenge, e4::sub(one.value[gate_bit], zero.value[gate_bit]), zero.value[gate_bit]);
  return result;
}

// Fold all three preceding coordinates exactly once. The published cache is
// subsequently read directly; the evaluator never invokes
// gkr_get_continuing_value, whose first_access path would perform an extra fold.
DEVICE_FORCEINLINE dr_window_e4_pair dr_window_fold_depth3_pair(const gkr_dr_cont_window3_desc &desc, const e4 *source, const size_t output_pair,
                                                                const bool active) {
  const e4 c0 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 3u) : e4::ZERO();
  const e4 c1 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 2u) : e4::ZERO();
  const e4 c2 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 1u) : e4::ZERO();
  dr_window_e4_pair level1[4];
#pragma unroll
  for (u32 pair = 0; pair < 4; ++pair) {
    const size_t leaf_pair = (output_pair << 3) + 2u * pair;
    const auto zero = dr_window_load_e4_pair_guarded(source, leaf_pair, active);
    const auto one = dr_window_load_e4_pair_guarded(source, leaf_pair + 1u, active);
    level1[pair] = dr_window_pair_fold(zero, one, c0);
  }
  const auto level2_0 = dr_window_pair_fold(level1[0], level1[1], c1);
  const auto level2_1 = dr_window_pair_fold(level1[2], level1[3], c1);
  return dr_window_pair_fold(level2_0, level2_1, c2);
}

DEVICE_FORCEINLINE void dr_window_continuation_prologue(const gkr_dr_cont_window3_desc &desc) {
  constexpr u32 work_count = DR_WINDOW_CONT_OCCURRENCES * DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t tile_pair_base = static_cast<size_t>(blockIdx.x) * DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t output_pair_count = static_cast<size_t>(1u) << (desc.log_rows + 3u);
  for (u32 work = threadIdx.x; work < work_count; work += blockDim.x) {
    const u32 occurrence = work / DR_WINDOW_CONT_PAIRS_PER_TILE;
    const u32 slot = occurrence / GKR_DIM_REDUCING_INPUTS_PER_SLOT;
    if ((desc.batch.enabled_mask & (1u << slot)) == 0)
      continue;
    const u32 operand = occurrence % GKR_DIM_REDUCING_INPUTS_PER_SLOT;
    const u32 tile_pair = work % DR_WINDOW_CONT_PAIRS_PER_TILE;
    const size_t output_pair = tile_pair_base + tile_pair;
    const auto source = gkr_resolve_dim_reducing_continuation_source<e4>(desc.batch.tables, desc.batch.slots[slot].io[operand]);
    const bool active = source.first_access && output_pair < output_pair_count;
    const auto folded = dr_window_fold_depth3_pair(desc, source.previous_layer_start, output_pair, active);
    if (active)
      store<dr_window_e4_pair, st_modifier::cs>(reinterpret_cast<dr_window_e4_pair *>(source.this_layer_start) + output_pair, folded);
  }
}

DEVICE_FORCEINLINE const e4 *dr_window_resolve_published_column(const gkr_dim_reducing_tables &tables, const gkr_source_record record) {
  u32 cache_slot;
  u32 cache_poly_idx;
  unpack_dim_reducing_cache_u16(record.cache, cache_slot, cache_poly_idx);
  const e4 *base = reinterpret_cast<const e4 *>(tables.bases[cache_slot]);
  return base + (static_cast<size_t>(cache_poly_idx) << tables.log2_stride[cache_slot]);
}

struct dr_window_continuation_gate_source {
  const e4 *column;
  u32 gate_bit;

  DEVICE_FORCEINLINE e4 value(const u32 y_index) const { return load<e4, ld_modifier::ca>(column, 2u * y_index + gate_bit); }
};

DEVICE_FORCEINLINE bwd_window_triplet<e4> dr_window_continuation_triplet(const e4 *column, const u32 row, const bwd_window_selector_pair selector,
                                                                         const u32 gate_bit) {
  const dr_window_continuation_gate_source source{column, gate_bit};
  const e4 zero = bwd_window_xy_endpoint<e4>(source, row, selector, 0);
  const e4 one = bwd_window_xy_endpoint<e4>(source, row, selector, 1);
  return {{zero, one, e4::sub(one, zero)}};
}

DEVICE_FORCEINLINE void dr_window_continuation_add_product(e4 (&total)[3], const bwd_window_triplet<e4> left, const bwd_window_triplet<e4> right,
                                                           const e4 coefficient) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2)
    total[x2] = e4::fma(coefficient, e4::mul(left.values[x2], right.values[x2]), total[x2]);
}

// These are the complete-tensor lifts of
// gkr_pairwise_continuation_accumulate and
// gkr_lookup_continuation_accumulate. Boolean cells retain the full fixed
// relation; no R0 materialized-output/product-excess rule participates.
DEVICE_FORCEINLINE void dr_window_continuation_accumulate_slot(const gkr_dr_cont_window3_desc &desc, const u32 slot_index, const u32 row,
                                                               const bwd_window_selector_pair selector, e4 (&total)[3]) {
  const gkr_dim_reducing_slot &slot = desc.batch.slots[slot_index];
  const e4 *inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
#pragma unroll
  for (u32 operand = 0; operand < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++operand)
    inputs[operand] = dr_window_resolve_published_column(desc.batch.tables, slot.io[operand]);

  e4 batch_challenges[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
  gkr_load_slot_batch_challenges(slot, batch_challenges);
  if ((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK & (1u << slot_index)) != 0) {
#pragma unroll
    for (u32 tower = 0; tower < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++tower) {
      const auto gate_zero = dr_window_continuation_triplet(inputs[tower], row, selector, 0);
      const auto gate_one = dr_window_continuation_triplet(inputs[tower], row, selector, 1);
      dr_window_continuation_add_product(total, gate_zero, gate_one, batch_challenges[tower]);
    }
  } else {
    const auto numerator_zero = dr_window_continuation_triplet(inputs[0], row, selector, 0);
    const auto numerator_one = dr_window_continuation_triplet(inputs[0], row, selector, 1);
    const auto denominator_zero = dr_window_continuation_triplet(inputs[1], row, selector, 0);
    const auto denominator_one = dr_window_continuation_triplet(inputs[1], row, selector, 1);
    dr_window_continuation_add_product(total, numerator_zero, denominator_one, batch_challenges[0]);
    dr_window_continuation_add_product(total, numerator_one, denominator_zero, batch_challenges[0]);
    dr_window_continuation_add_product(total, denominator_zero, denominator_one, batch_challenges[1]);
  }
}

// The tail is deliberately DR-specific because bwd_window_publish accepts a
// main-window descriptor. The CPU source-parity gate pins the cell index,
// inactive-row zeroing, global Eq read, warp reduction, and row-tile store.
DEVICE_FORCEINLINE void dr_window_continuation_publish(const gkr_dr_cont_window3_desc &desc, const u32 row_tile, const u32 lane, const bool active,
                                                       const bwd_window_selector_pair selector, const e4 (&values)[3]) {
  const u32 safe_row = active ? row_tile * BWD_WINDOW_ROWS_PER_TILE + lane : 0;
  const e4 equality = gkr_compute_eq_inline_global<e4>(desc.eq_high_0, desc.eq_high_1, desc.batch.eq_low, desc.batch.eq_sizes, safe_row);
  const u32 cell_base = 3 * selector.x1 + selector.x0;
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    e4 value = active ? e4::mul(equality, values[x2]) : e4::ZERO();
    value = bwd_window_warp_sum(value);
    if (lane == 0)
      store<e4, st_modifier::cs>(desc.partials, value, static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + 9 * x2 + cell_base);
  }
}

DEVICE_FORCEINLINE void dr_window_continuation(const gkr_dr_cont_window3_desc &desc) {
  dr_window_continuation_prologue(desc);
  __syncthreads();

  const u32 lane = bwd_window_lane();
  const u32 row_tile = bwd_window_row_tile();
  const u32 row = row_tile * BWD_WINDOW_ROWS_PER_TILE + lane;
  const u32 row_count = 1u << desc.log_rows;
  const bool active = row < row_count;
  const u32 safe_row = active ? row : 0;
  const auto selector = bwd_window_selector(bwd_window_selector_id());
  e4 values[3] = {e4::ZERO(), e4::ZERO(), e4::ZERO()};

#pragma unroll
  for (u32 slot = 0; slot < GKR_DIM_REDUCING_SLOTS; ++slot) {
    if ((desc.batch.enabled_mask & (1u << slot)) != 0)
      dr_window_continuation_accumulate_slot(desc, slot, safe_row, selector, values);
  }
  dr_window_continuation_publish(desc, row_tile, lane, active, selector, values);
}

} // namespace airbender::gkr::backward
