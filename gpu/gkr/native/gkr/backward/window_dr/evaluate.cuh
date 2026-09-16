#pragma once

#include "../window/window_geometry.cuh"
#include "abi.cuh"
#include "math_accumulator_packed.cuh"

namespace airbender::gkr::backward {

struct dr_window_gate_pairs {
  bwd_window_pair<e4> gate[2];
};

using dr_window_corner_quad = bwd_window_packed_values<e4, 4>;

DEVICE_FORCEINLINE dr_window_corner_quad dr_window_load_corner_quad(const e4 *column, const u32 row, const u32 bit0, const u32 bit1) {
  return bwd_window_load<e4, 4>(column, 2u * bwd_window_corner_index(row, bit0, bit1, 0));
}

DEVICE_FORCEINLINE dr_window_corner_quad dr_window_quad_sub(const dr_window_corner_quad one, const dr_window_corner_quad zero) {
  dr_window_corner_quad result;
#pragma unroll
  for (u32 index = 0; index < 4; ++index)
    result.values[index] = e4::sub(one.values[index], zero.values[index]);
  return result;
}

// Same collapse as bwd_window_xy_endpoint, applied once to the whole quad.
DEVICE_FORCEINLINE dr_window_gate_pairs dr_window_packed_gate_pairs(const e4 *column, const u32 row, const bwd_window_selector_pair selector) {
  const u32 bit0_zero = selector.x0_infinity() ? 0 : selector.x0;
  const u32 bit1_zero = selector.x1_infinity() ? 0 : selector.x1;
  const dr_window_corner_quad corner00 = dr_window_load_corner_quad(column, row, bit0_zero, bit1_zero);
  dr_window_corner_quad at_x1_zero = corner00;
  if (selector.x0_infinity())
    at_x1_zero = dr_window_quad_sub(dr_window_load_corner_quad(column, row, 1, bit1_zero), corner00);
  dr_window_corner_quad value = at_x1_zero;
  if (selector.x1_infinity()) {
    const dr_window_corner_quad corner01 = dr_window_load_corner_quad(column, row, bit0_zero, 1);
    dr_window_corner_quad at_x1_one = corner01;
    if (selector.x0_infinity())
      at_x1_one = dr_window_quad_sub(dr_window_load_corner_quad(column, row, 1, 1), corner01);
    value = dr_window_quad_sub(at_x1_one, at_x1_zero);
  }
  dr_window_gate_pairs result;
  result.gate[0] = {{value.values[0], value.values[2]}};
  result.gate[1] = {{value.values[1], value.values[3]}};
  return result;
}

DEVICE_FORCEINLINE bwd_window_triplet<e4> dr_window_add_triplets(const bwd_window_triplet<e4> a, const bwd_window_triplet<e4> b) {
  return {{e4::add(a.values[0], b.values[0]), e4::add(a.values[1], b.values[1]), e4::add(a.values[2], b.values[2])}};
}

DEVICE_FORCEINLINE const e4 *dr_window_resolve_column(const gkr_dr_window3_desc &desc, const gkr_source_record record) {
  return gkr_resolve_dim_reducing_initial_source<e4>(desc.batch.tables, record).start;
}

DEVICE_FORCEINLINE const e4 *dr_window_resolve_column(const gkr_dr_cont_window3_desc &desc, const gkr_source_record record) {
  u32 cache_slot, cache_poly_idx;
  unpack_dim_reducing_cache_u16(record.cache, cache_slot, cache_poly_idx);
  const e4 *base = reinterpret_cast<const e4 *>(desc.batch.tables.bases[cache_slot]);
  return base + (static_cast<size_t>(cache_poly_idx) << desc.batch.tables.log2_stride[cache_slot]);
}

DEVICE_FORCEINLINE e4 dr_window_eq(const gkr_dr_window3_desc &desc, const u32 row) {
  return gkr_compute_eq_inline<e4>(desc.batch.eq_low, desc.batch.eq_sizes, row);
}

DEVICE_FORCEINLINE e4 dr_window_eq(const gkr_dr_cont_window3_desc &desc, const u32 row) {
  return gkr_compute_eq_inline_global<e4>(desc.eq_high_0, desc.eq_high_1, desc.batch.eq_low, desc.batch.eq_sizes, row);
}

template <u32 SLOT, typename Descriptor>
DEVICE_FORCEINLINE void dr_window_recompute_slot_body(const Descriptor &desc, const u32 row, const bwd_window_selector_pair selector,
                                                      dr_window_packed_carry_e4 (&total)[3]) {
  static_assert(SLOT < GKR_DIM_REDUCING_SLOTS, "DR slot index out of range");
  const gkr_dim_reducing_slot &slot = desc.batch.slots[SLOT];
  const e4 *inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
#pragma unroll
  for (u32 operand = 0; operand < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++operand)
    inputs[operand] = dr_window_resolve_column(desc, slot.io[operand]);

  e4 batch_challenges[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
  gkr_load_slot_batch_challenges(slot, batch_challenges);

  if constexpr ((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK & (1u << SLOT)) != 0) {
#pragma unroll
    for (u32 tower = 0; tower < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++tower) {
      const auto gates = dr_window_packed_gate_pairs(inputs[tower], row, selector);
      dr_window_accumulate_triplet(total, bwd_window_endpoint_product<e4, e4>(gates.gate[0], gates.gate[1]), batch_challenges[tower]);
    }
  } else {
    const auto numerator = dr_window_packed_gate_pairs(inputs[0], row, selector);
    const auto denominator = dr_window_packed_gate_pairs(inputs[1], row, selector);
    const auto numerator_tensor = dr_window_add_triplets(bwd_window_endpoint_product<e4, e4>(numerator.gate[0], denominator.gate[1]),
                                                         bwd_window_endpoint_product<e4, e4>(numerator.gate[1], denominator.gate[0]));
    const auto denominator_tensor = bwd_window_endpoint_product<e4, e4>(denominator.gate[0], denominator.gate[1]);
    dr_window_accumulate_triplet(total, numerator_tensor, batch_challenges[0]);
    dr_window_accumulate_triplet(total, denominator_tensor, batch_challenges[1]);
  }
}

template <typename Descriptor> DEVICE_FORCEINLINE void dr_window_evaluate(const Descriptor &desc, const u32 effective_mask, const size_t tile_slot) {
  const u32 lane = bwd_window_lane();
  const u32 row_tile = bwd_window_row_tile();
  const u32 row = row_tile * BWD_WINDOW_ROWS_PER_TILE + lane;
  const bool active = row < (1u << desc.log_rows);
  const u32 safe_row = active ? row : 0;
  const auto selector = bwd_window_selector(bwd_window_selector_id());
  dr_window_packed_carry_e4 total[3] = {};
  if (effective_mask & (1u << 0))
    dr_window_recompute_slot_body<0>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 1))
    dr_window_recompute_slot_body<1>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 2))
    dr_window_recompute_slot_body<2>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 3))
    dr_window_recompute_slot_body<3>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 4))
    dr_window_recompute_slot_body<4>(desc, safe_row, selector, total);
  const e4 values[3] = {total[0].reduce(), total[1].reduce(), total[2].reduce()};
  const e4 equality = dr_window_eq(desc, safe_row);
  bwd_window_publish(desc.partials, tile_slot, lane, active, selector, equality, values);
}

} // namespace airbender::gkr::backward
