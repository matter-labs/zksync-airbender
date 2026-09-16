#pragma once
#include "continuation.cuh"
#include "math_accumulator_packed.cuh"
namespace airbender::gkr::backward {

DEVICE_FORCEINLINE bwd_window_triplet<e4> dr_cont_recompute_product_tensor(const bwd_window_pair<e4> a, const bwd_window_pair<e4> b) {
  return {
      {e4::mul(a.values[0], b.values[0]), e4::mul(a.values[1], b.values[1]), e4::mul(e4::sub(a.values[1], a.values[0]), e4::sub(b.values[1], b.values[0]))}};
}

struct dr_cont_gate_pairs {
  bwd_window_pair<e4> gate[2];
};

using dr_cont_corner_quad = bwd_window_packed_values<e4, 4>;

DEVICE_FORCEINLINE dr_cont_corner_quad dr_cont_load_corner_quad(const e4 *column, const u32 row, const u32 bit0, const u32 bit1) {
  return bwd_window_load<e4, 4>(column, 2u * bwd_window_corner_index(row, bit0, bit1, 0));
}

DEVICE_FORCEINLINE dr_cont_corner_quad dr_cont_quad_sub(const dr_cont_corner_quad one, const dr_cont_corner_quad zero) {
  dr_cont_corner_quad result;
#pragma unroll
  for (u32 index = 0; index < 4; ++index)
    result.values[index] = e4::sub(one.values[index], zero.values[index]);
  return result;
}

// Same collapse as bwd_window_xy_endpoint, applied once to the whole quad.
DEVICE_FORCEINLINE dr_cont_gate_pairs dr_cont_packed_gate_pairs(const e4 *column, const u32 row, const bwd_window_selector_pair selector) {
  const u32 bit0_zero = selector.x0_infinity() ? 0 : selector.x0;
  const u32 bit1_zero = selector.x1_infinity() ? 0 : selector.x1;
  const dr_cont_corner_quad corner00 = dr_cont_load_corner_quad(column, row, bit0_zero, bit1_zero);
  dr_cont_corner_quad at_x1_zero = corner00;
  if (selector.x0_infinity())
    at_x1_zero = dr_cont_quad_sub(dr_cont_load_corner_quad(column, row, 1, bit1_zero), corner00);
  dr_cont_corner_quad value = at_x1_zero;
  if (selector.x1_infinity()) {
    const dr_cont_corner_quad corner01 = dr_cont_load_corner_quad(column, row, bit0_zero, 1);
    dr_cont_corner_quad at_x1_one = corner01;
    if (selector.x0_infinity())
      at_x1_one = dr_cont_quad_sub(dr_cont_load_corner_quad(column, row, 1, 1), corner01);
    value = dr_cont_quad_sub(at_x1_one, at_x1_zero);
  }
  dr_cont_gate_pairs result;
  result.gate[0] = {{value.values[0], value.values[2]}};
  result.gate[1] = {{value.values[1], value.values[3]}};
  return result;
}

template <u32 SLOT>
DEVICE_FORCEINLINE void dr_cont_recompute_slot_body(const gkr_dr_cont_window3_desc &desc, const u32 row, const bwd_window_selector_pair selector,
                                                    dr_window_packed_carry_e4 (&total)[3]) {
  static_assert(SLOT < GKR_DIM_REDUCING_SLOTS, "DR slot index out of range");
  const gkr_dim_reducing_slot &slot = desc.batch.slots[SLOT];
  const e4 *inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
#pragma unroll
  for (u32 operand = 0; operand < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++operand)
    inputs[operand] = dr_window_resolve_published_column(desc.batch.tables, slot.io[operand]);

  e4 batch_challenges[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
  gkr_load_slot_batch_challenges(slot, batch_challenges);

  if constexpr ((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK & (1u << SLOT)) != 0) {
#pragma unroll
    for (u32 tower = 0; tower < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++tower) {
      const auto gates = dr_cont_packed_gate_pairs(inputs[tower], row, selector);
      dr_window_accumulate_triplet(total, dr_cont_recompute_product_tensor(gates.gate[0], gates.gate[1]), batch_challenges[tower]);
    }
  } else {
    const auto numerator = dr_cont_packed_gate_pairs(inputs[0], row, selector);
    const auto denominator = dr_cont_packed_gate_pairs(inputs[1], row, selector);
    const auto numerator_tensor = dr_window_add_triplets(dr_cont_recompute_product_tensor(numerator.gate[0], denominator.gate[1]),
                                                         dr_cont_recompute_product_tensor(numerator.gate[1], denominator.gate[0]));
    const auto denominator_tensor = dr_cont_recompute_product_tensor(denominator.gate[0], denominator.gate[1]);
    dr_window_accumulate_triplet(total, numerator_tensor, batch_challenges[0]);
    dr_window_accumulate_triplet(total, denominator_tensor, batch_challenges[1]);
  }
}

// First combine the four rows in each quartet, then give one x2 cell to
// each of roles 0..2. XOR masks 4/8/16 preserve the role while summing the
// eight quartets. All lanes participate; role 3 carries initialized zero.
DEVICE_FORCEINLINE e4 dr_cont_shuffle_add(const e4 value, const u32 mask) {
  e4 other;
  *reinterpret_cast<uint4 *>(&other) = shfl_xor(0xffffffffu, *reinterpret_cast<const uint4 *>(&value), mask, BWD_WINDOW_WARP_LANES);
  return e4::add(value, other);
}

DEVICE_FORCEINLINE void dr_cont_quartet_publish(const gkr_dr_cont_window3_desc &desc, const size_t tile_slot, const u32 lane, const bool active,
                                                const u32 safe_row, const bwd_window_selector_pair selector, const e4 (&values)[3]) {
  const e4 equality = gkr_compute_eq_inline_global<e4>(desc.eq_high_0, desc.eq_high_1, desc.batch.eq_low, desc.batch.eq_sizes, safe_row);
  e4 sums[3];
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    sums[x2] = active ? e4::mul(equality, values[x2]) : e4::ZERO();
    sums[x2] = dr_cont_shuffle_add(sums[x2], 1);
    sums[x2] = dr_cont_shuffle_add(sums[x2], 2);
  }
  const u32 role = lane & 3u;
  e4 value = role == 0 ? sums[0] : role == 1 ? sums[1] : role == 2 ? sums[2] : e4::ZERO();
#pragma unroll
  for (u32 mask = 4; mask < BWD_WINDOW_WARP_LANES; mask <<= 1)
    value = dr_cont_shuffle_add(value, mask);
  if (lane < 3) {
    store<e4, st_modifier::cs>(desc.partials, value, tile_slot * BWD_WINDOW_TENSOR_CELLS + 9 * lane + 3 * selector.x1 + selector.x0);
  }
}

} // namespace airbender::gkr::backward
