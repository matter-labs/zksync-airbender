#pragma once

#include "abi_pr.cuh"

namespace airbender::gkr::proth120::backward {

using pr_dr_window_pair = pr_dr_bwd::bwd_window_pair<pr>;
using pr_dr_window_triplet = pr_dr_bwd::bwd_window_triplet<pr>;
using pr_dr_window_corner_quad = pr_dr_bwd::bwd_window_packed_values<pr, 4>;

struct pr_dr_window_gate_pairs {
  pr_dr_window_pair gate[2];
};

DEVICE_FORCEINLINE pr_dr_window_corner_quad pr_dr_window_load_corner_quad(const pr *column, const u32 row, const u32 bit0, const u32 bit1) {
  return pr_dr_bwd::bwd_window_load<pr, 4>(column, 2u * pr_dr_bwd::bwd_window_corner_index(row, bit0, bit1, 0));
}

DEVICE_FORCEINLINE pr_dr_window_corner_quad pr_dr_window_quad_sub(const pr_dr_window_corner_quad one, const pr_dr_window_corner_quad zero) {
  pr_dr_window_corner_quad result;
#pragma unroll
  for (u32 index = 0; index < 4; ++index)
    result.values[index] = pr::sub(one.values[index], zero.values[index]);
  return result;
}

DEVICE_FORCEINLINE pr_dr_window_gate_pairs pr_dr_window_packed_gate_pairs(const pr *column, const u32 row, const pr_dr_bwd::bwd_window_selector_pair selector) {
  const u32 bit0_zero = selector.x0_infinity() ? 0 : selector.x0;
  const u32 bit1_zero = selector.x1_infinity() ? 0 : selector.x1;
  const pr_dr_window_corner_quad corner00 = pr_dr_window_load_corner_quad(column, row, bit0_zero, bit1_zero);
  pr_dr_window_corner_quad at_x1_zero = corner00;
  if (selector.x0_infinity())
    at_x1_zero = pr_dr_window_quad_sub(pr_dr_window_load_corner_quad(column, row, 1, bit1_zero), corner00);
  pr_dr_window_corner_quad value = at_x1_zero;
  if (selector.x1_infinity()) {
    const pr_dr_window_corner_quad corner01 = pr_dr_window_load_corner_quad(column, row, bit0_zero, 1);
    pr_dr_window_corner_quad at_x1_one = corner01;
    if (selector.x0_infinity())
      at_x1_one = pr_dr_window_quad_sub(pr_dr_window_load_corner_quad(column, row, 1, 1), corner01);
    value = pr_dr_window_quad_sub(at_x1_one, at_x1_zero);
  }
  pr_dr_window_gate_pairs result;
  result.gate[0] = {{value.values[0], value.values[2]}};
  result.gate[1] = {{value.values[1], value.values[3]}};
  return result;
}

DEVICE_FORCEINLINE pr_dr_window_triplet pr_dr_window_endpoint_product(const pr_dr_window_pair a, const pr_dr_window_pair b) {
  const pr leading = pr::mul(pr::sub(a.values[1], a.values[0]), pr::sub(b.values[1], b.values[0]));
  return {{pr::mul(a.values[0], b.values[0]), pr::mul(a.values[1], b.values[1]), leading}};
}

DEVICE_FORCEINLINE pr_dr_window_triplet pr_dr_window_add_triplets(const pr_dr_window_triplet a, const pr_dr_window_triplet b) {
  return {{pr::add(a.values[0], b.values[0]), pr::add(a.values[1], b.values[1]), pr::add(a.values[2], b.values[2])}};
}

DEVICE_FORCEINLINE void pr_dr_window_accumulate(PrSum32 (&total)[3], const pr_dr_window_triplet value, const pr coefficient) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2)
    total[x2].add(pr::mul(coefficient, value.values[x2]));
}

template <bool CONTINUATION> DEVICE_FORCEINLINE const pr *pr_dr_window_resolve_column(const pr_dr_window_desc &desc, const gkr_source_record record) {
  if constexpr (CONTINUATION) {
    u32 cache_slot, cache_poly_idx;
    unpack_dim_reducing_cache_u16(record.cache, cache_slot, cache_poly_idx);
    const pr *base = reinterpret_cast<const pr *>(desc.batch.tables.bases[cache_slot]);
    return base + (static_cast<size_t>(cache_poly_idx) << desc.batch.tables.log2_stride[cache_slot]);
  } else {
    return gkr_resolve_dim_reducing_initial_source<pr>(desc.batch.tables, record).start;
  }
}

template <u32 SLOT, bool CONTINUATION>
DEVICE_FORCEINLINE void pr_dr_window_slot_body(const pr_dr_window_desc &desc, const u32 row, const pr_dr_bwd::bwd_window_selector_pair selector,
                                               PrSum32 (&total)[3]) {
  static_assert(SLOT < GKR_DIM_REDUCING_SLOTS, "DR slot index out of range");
  const gkr_dim_reducing_slot &slot = desc.batch.slots[SLOT];
  const pr *inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
#pragma unroll
  for (u32 operand = 0; operand < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++operand)
    inputs[operand] = pr_dr_window_resolve_column<CONTINUATION>(desc, slot.inputs[operand]);

  pr batch_challenges[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
#pragma unroll
  for (u32 output = 0; output < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++output)
    batch_challenges[output] = load<pr, ld_modifier::ca>(desc.batch_challenges, slot.batch_exp[output]);

  if constexpr ((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK & (1u << SLOT)) != 0) {
#pragma unroll
    for (u32 tower = 0; tower < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++tower) {
      const auto gates = pr_dr_window_packed_gate_pairs(inputs[tower], row, selector);
      pr_dr_window_accumulate(total, pr_dr_window_endpoint_product(gates.gate[0], gates.gate[1]), batch_challenges[tower]);
    }
  } else {
    const auto numerator = pr_dr_window_packed_gate_pairs(inputs[0], row, selector);
    const auto denominator = pr_dr_window_packed_gate_pairs(inputs[1], row, selector);
    const auto numerator_tensor = pr_dr_window_add_triplets(pr_dr_window_endpoint_product(numerator.gate[0], denominator.gate[1]),
                                                            pr_dr_window_endpoint_product(numerator.gate[1], denominator.gate[0]));
    const auto denominator_tensor = pr_dr_window_endpoint_product(denominator.gate[0], denominator.gate[1]);
    pr_dr_window_accumulate(total, numerator_tensor, batch_challenges[0]);
    pr_dr_window_accumulate(total, denominator_tensor, batch_challenges[1]);
  }
}

DEVICE_FORCEINLINE pr pr_dr_window_quartet_shuffle_add(const pr value, const u32 mask) {
  return pr::add(value, shfl_xor(0xffffffffu, value, mask, BWD_WINDOW_WARP_LANES));
}

DEVICE_FORCEINLINE void pr_dr_window_publish(pr *partials, const size_t tile_slot, const u32 lane, const bool active,
                                             const pr_dr_bwd::bwd_window_selector_pair selector, const pr equality, const pr (&values)[3]) {
  pr sums[3];
  const pr weight = active ? equality : pr_zero();
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    sums[x2] = pr::mul(weight, values[x2]);
    sums[x2] = pr_dr_window_quartet_shuffle_add(sums[x2], 1);
    sums[x2] = pr_dr_window_quartet_shuffle_add(sums[x2], 2);
  }
  const u32 role = lane & 3u;
  pr value = role == 0 ? sums[0] : role == 1 ? sums[1] : role == 2 ? sums[2] : pr_zero();
#pragma unroll
  for (u32 mask = 4; mask < BWD_WINDOW_WARP_LANES; mask <<= 1)
    value = pr_dr_window_quartet_shuffle_add(value, mask);
  if (lane < 3)
    store<pr, st_modifier::cs>(partials, value, tile_slot * pr_dr_bwd::BWD_WINDOW_TENSOR_CELLS + 9 * lane + 3 * selector.x1 + selector.x0);
}

template <bool CONTINUATION> DEVICE_FORCEINLINE void pr_dr_window_evaluate(const pr_dr_window_desc &desc, const u32 effective_mask, const size_t tile_slot) {
  const u32 lane = pr_dr_bwd::bwd_window_lane();
  const u32 row_tile = pr_dr_bwd::bwd_window_row_tile();
  const u32 row = row_tile * pr_dr_bwd::BWD_WINDOW_ROWS_PER_TILE + lane;
  const bool active = row < (1u << desc.log_rows);
  const u32 safe_row = active ? row : 0;
  const auto selector = pr_dr_bwd::bwd_window_selector(pr_dr_bwd::bwd_window_selector_id());
  PrSum32 total[3] = {PrSum32::zero(), PrSum32::zero(), PrSum32::zero()};
  if (effective_mask & (1u << 0))
    pr_dr_window_slot_body<0, CONTINUATION>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 1))
    pr_dr_window_slot_body<1, CONTINUATION>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 2))
    pr_dr_window_slot_body<2, CONTINUATION>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 3))
    pr_dr_window_slot_body<3, CONTINUATION>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 4))
    pr_dr_window_slot_body<4, CONTINUATION>(desc, safe_row, selector, total);
  const pr values[3] = {total[0].flush(), total[1].flush(), total[2].flush()};
  const pr equality = gkr_compute_eq_inline_global<pr>(desc.eq_high_0, desc.eq_high_1, desc.batch.eq_low, desc.batch.eq_sizes, safe_row);
  pr_dr_window_publish(desc.partials, tile_slot, lane, active, selector, equality, values);
}

} // namespace airbender::gkr::proth120::backward
