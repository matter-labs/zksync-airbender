#pragma once

#include "gkr/backward/window_dr/corner_quad.cuh"

namespace airbender::gkr::backward {

template <typename F> struct dr_window_gate_pairs {
  bwd_window_pair<F> gate[2];
};

template <typename F>
DEVICE_FORCEINLINE dr_window_gate_pairs<F> dr_window_packed_gate_pairs(const F *column, const u32 row, const bwd_window_selector_pair selector) {
  const u32 bit0_zero = selector.x0_infinity() ? 0 : selector.x0;
  const u32 bit1_zero = selector.x1_infinity() ? 0 : selector.x1;
  const bwd_window_packed_values<F, 4> corner00 = dr_window_load_corner_quad(column, row, bit0_zero, bit1_zero);
  bwd_window_packed_values<F, 4> at_x1_zero = corner00;
  if (selector.x0_infinity())
    at_x1_zero = dr_window_quad_sub(dr_window_load_corner_quad(column, row, 1, bit1_zero), corner00);
  bwd_window_packed_values<F, 4> value = at_x1_zero;
  if (selector.x1_infinity()) {
    const bwd_window_packed_values<F, 4> corner01 = dr_window_load_corner_quad(column, row, bit0_zero, 1);
    bwd_window_packed_values<F, 4> at_x1_one = corner01;
    if (selector.x0_infinity())
      at_x1_one = dr_window_quad_sub(dr_window_load_corner_quad(column, row, 1, 1), corner01);
    value = dr_window_quad_sub(at_x1_one, at_x1_zero);
  }
  dr_window_gate_pairs<F> result;
  result.gate[0] = {{value.values[0], value.values[2]}};
  result.gate[1] = {{value.values[1], value.values[3]}};
  return result;
}

template <typename F> DEVICE_FORCEINLINE bwd_window_triplet<F> dr_window_add_triplets(const bwd_window_triplet<F> a, const bwd_window_triplet<F> b) {
  return {{F::add(a.values[0], b.values[0]), F::add(a.values[1], b.values[1]), F::add(a.values[2], b.values[2])}};
}

} // namespace airbender::gkr::backward
