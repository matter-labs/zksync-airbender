#pragma once
#include "../window/window_geometry.cuh"
#include "../window/window_source.cuh"
namespace airbender::gkr::backward {
template <typename F>
DEVICE_FORCEINLINE bwd_window_packed_values<F, 4> dr_window_load_corner_quad(const F *column, const u32 row, const u32 bit0, const u32 bit1) {
  return bwd_window_load<F, 4>(column, 2u * bwd_window_corner_index(row, bit0, bit1, 0));
}
template <typename F>
DEVICE_FORCEINLINE bwd_window_packed_values<F, 4> dr_window_quad_sub(const bwd_window_packed_values<F, 4> one, const bwd_window_packed_values<F, 4> zero) {
  bwd_window_packed_values<F, 4> result;
#pragma unroll
  for (u32 index = 0; index < 4; ++index)
    result.values[index] = F::sub(one.values[index], zero.values[index]);
  return result;
}
} // namespace airbender::gkr::backward
