#pragma once

#include "../../support/lookup_helpers.cuh"
#include "../window/window_geometry.cuh"

namespace airbender::gkr::backward {

// DR R0 is the only pass in this launch: its factored Eq high slabs are built
// before this producer and read through gkr_compute_eq_inline exactly once per
// row. A future continuation must use gkr_compute_eq_inline_global (or another
// caller-supplied reader); writing and reading the process-wide constant slab
// inside one continuation launch is prohibited.
struct alignas(16) gkr_dr_window3_desc {
  gkr_dim_reducing_batch<e4> batch;
  e4 *partials;
  u32 log_rows;
  u32 reserved;
};

static_assert(sizeof(gkr_dr_window3_desc) == 352, "gkr_dr_window3_desc/DrWindowLaunchBinding ABI size drift");
static_assert(alignof(gkr_dr_window3_desc) == 16, "gkr_dr_window3_desc ABI alignment drift");
static_assert(sizeof(gkr_dr_window3_desc) <= BWD_SEG_DESC_CAP, "gkr_dr_window3_desc exceeds the CUDA kernel-argument ceiling");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, batch) == 0, "DR batch ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, partials) == 336, "DR partials ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, log_rows) == 344, "DR log_rows ABI offset drift");
static_assert(__builtin_offsetof(gkr_dr_window3_desc, reserved) == 348, "DR reserved ABI offset drift");
static_assert(GKR_DIM_REDUCING_INPUTS_PER_SLOT == GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, "DR pairwise tower and batch-challenge cardinalities must match");

struct dr_window_input_gate_source {
  const e4 *column;
  u32 gate_bit;

  DEVICE_FORCEINLINE e4 value(const u32 y_index) const {
    // The retained gate bit is the low physical axis: 2 * Y + b.
    // The nine selector warps reuse overlapping corners from this column.
    return load<e4, ld_modifier::ca>(column, 2u * y_index + gate_bit);
  }
};

DEVICE_FORCEINLINE bwd_window_pair<e4> dr_window_input_pair(const e4 *column, const u32 row, const bwd_window_selector_pair selector, const u32 gate_bit) {
  const dr_window_input_gate_source source{column, gate_bit};
  return {{bwd_window_xy_endpoint<e4>(source, row, selector, 0), bwd_window_xy_endpoint<e4>(source, row, selector, 1)}};
}

DEVICE_FORCEINLINE bwd_window_pair<e4> dr_window_output_pair(const e4 *column, const u32 row, const bwd_window_selector_pair selector) {
  return bwd_window_pair_values(bwd_window_direct_e4_source{column}, row, selector);
}

DEVICE_FORCEINLINE void dr_window_accumulate_triplet(e4 (&total)[3], const bwd_window_triplet<e4> value, const e4 coefficient) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2)
    total[x2] = e4::fma(coefficient, value.values[x2], total[x2]);
}

DEVICE_FORCEINLINE bwd_window_triplet<e4> dr_window_add_triplets(const bwd_window_triplet<e4> a, const bwd_window_triplet<e4> b) {
  return {{e4::add(a.values[0], b.values[0]), e4::add(a.values[1], b.values[1]), e4::add(a.values[2], b.values[2])}};
}

DEVICE_FORCEINLINE void dr_window_accumulate_slot(const gkr_dr_window3_desc &desc, const u32 slot_index, const u32 row, const bwd_window_selector_pair selector,
                                                  e4 (&total)[3]) {
  const gkr_dim_reducing_slot &slot = desc.batch.slots[slot_index];
  gkr_ext_initial_source<e4> inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
  gkr_ext_initial_source<e4> outputs[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
#pragma unroll
  for (u32 operand = 0; operand < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++operand)
    inputs[operand] = gkr_resolve_dim_reducing_initial_source<e4>(desc.batch.tables, slot.io[operand]);
#pragma unroll
  for (u32 operand = 0; operand < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++operand)
    outputs[operand] = gkr_resolve_dim_reducing_initial_source<e4>(desc.batch.tables, slot.io[GKR_DIM_REDUCING_INPUTS_PER_SLOT + operand]);

  e4 batch_challenges[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
  gkr_load_slot_batch_challenges(slot, batch_challenges);

  if ((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK & (1u << slot_index)) != 0) {
#pragma unroll
    for (u32 tower = 0; tower < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++tower) {
      const auto gate0 = dr_window_input_pair(inputs[tower].start, row, selector, 0);
      const auto gate1 = dr_window_input_pair(inputs[tower].start, row, selector, 1);
      dr_window_accumulate_triplet(total, bwd_window_product_tensor(gate0, gate1, selector), batch_challenges[tower]);
    }
  } else {
    const auto numerator0 = dr_window_input_pair(inputs[0].start, row, selector, 0);
    const auto numerator1 = dr_window_input_pair(inputs[0].start, row, selector, 1);
    const auto denominator0 = dr_window_input_pair(inputs[1].start, row, selector, 0);
    const auto denominator1 = dr_window_input_pair(inputs[1].start, row, selector, 1);
    const auto numerator =
        dr_window_add_triplets(bwd_window_product_tensor(numerator0, denominator1, selector), bwd_window_product_tensor(numerator1, denominator0, selector));
    const auto denominator = bwd_window_product_tensor(denominator0, denominator1, selector);
    dr_window_accumulate_triplet(total, numerator, batch_challenges[0]);
    dr_window_accumulate_triplet(total, denominator, batch_challenges[1]);
  }

  // Forward outputs are materialized values, not another product polynomial:
  // they contribute only at the eight Boolean selector cells.
  if (!selector.has_infinity()) {
#pragma unroll
    for (u32 output = 0; output < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++output) {
      const auto values = dr_window_output_pair(outputs[output].start, row, selector);
      total[0] = e4::fma(batch_challenges[output], values.values[0], total[0]);
      total[1] = e4::fma(batch_challenges[output], values.values[1], total[1]);
    }
  }
}

// One 288-thread block owns a row tile. Nine warps enumerate (x0, x1), and
// each lane owns one suffix row. The published tensor is row-tile-major in the
// tail's round order: 9 * x2 + 3 * x1 + x0.
DEVICE_FORCEINLINE void dr_window_r0(const gkr_dr_window3_desc &desc) {
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
      dr_window_accumulate_slot(desc, slot, safe_row, selector, values);
  }

  // This publish tail deliberately duplicates bwd_window_publish because its
  // descriptor type is DR-specific. The Rust source-parity gate pins the
  // shared index, inactive-row zeroing, Eq read, reduction, and store contract.
  const e4 equality = gkr_compute_eq_inline<e4>(desc.batch.eq_low, desc.batch.eq_sizes, safe_row);
  const u32 cell_base = 3 * selector.x1 + selector.x0;
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    e4 value = active ? e4::mul(equality, values[x2]) : e4::ZERO();
    value = bwd_window_warp_sum(value);
    if (lane == 0)
      store<e4, st_modifier::cs>(desc.partials, value, static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + 9 * x2 + cell_base);
  }
}

} // namespace airbender::gkr::backward
