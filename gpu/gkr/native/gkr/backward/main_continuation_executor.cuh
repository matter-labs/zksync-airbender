#pragma once

#include "gkr/backward/window/common.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_MAIN_CONT_DYNAMIC_X0 = 3;
constexpr u32 BWD_MAIN_CONT_BOOLEAN_X0 = BWD_MAIN_CONT_DYNAMIC_X0 + 1;

// Adjacent x2 corners occupy one aligned 32-byte sector and can share a load.
template <u32 X0, typename Pair, typename F> DEVICE_FORCEINLINE Pair bwd_main_cont_resolve_x0_pair(const F *corners, const u32 x1, const u32 dynamic_x0) {
  const auto *pairs = reinterpret_cast<const Pair *>(corners);
  if constexpr (X0 == BWD_MAIN_CONT_BOOLEAN_X0)
    return load<Pair, ld_modifier::ca>(pairs + x1 + 2 * dynamic_x0);
  const u32 x0 = X0 == BWD_MAIN_CONT_DYNAMIC_X0 ? dynamic_x0 : X0;
  if (x0 == 0)
    return load<Pair, ld_modifier::ca>(pairs + x1);
  if (x0 == 1)
    return load<Pair, ld_modifier::ca>(pairs + x1 + 2);
  const Pair zero = load<Pair, ld_modifier::ca>(pairs + x1);
  const Pair one = load<Pair, ld_modifier::ca>(pairs + x1 + 2);
  return Pair{{F::sub(one.value[0], zero.value[0]), F::sub(one.value[1], zero.value[1])}};
}

template <typename Triplet, typename F> DEVICE_FORCEINLINE void bwd_main_cont_add_scaled(const Triplet &values, const F &coefficient, F (&accumulator)[3]) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; x2++)
    accumulator[x2] = F::fma(coefficient, values.value[x2], accumulator[x2]);
}

template <typename Triplet, typename F>
DEVICE_FORCEINLINE void bwd_main_cont_add_product(const Triplet &lhs, const Triplet &rhs, const F &coefficient, F (&accumulator)[3]) {
#pragma unroll
  for (u32 x2 = 0; x2 < 3; x2++)
    accumulator[x2] = F::fma(coefficient, F::mul(lhs.value[x2], rhs.value[x2]), accumulator[x2]);
}

} // namespace airbender::gkr::backward
