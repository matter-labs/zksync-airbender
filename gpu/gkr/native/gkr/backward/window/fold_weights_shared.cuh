#pragma once
#include "common.cuh"
namespace airbender::gkr {
template <typename F, typename Point> DEVICE_FORCEINLINE void build_fold_weights(F *fold_weights, const Point point, const u32 round) {
  const u32 slot = threadIdx.x;
  if (blockIdx.x != 0 || slot >= BWD_FOLD_WEIGHT_SLOTS)
    return;
  const u32 delta = slot < BWD_FOLD_WEIGHT_BASE_D2 ? 1 : slot < BWD_FOLD_WEIGHT_BASE_D3 ? 2 : 3;
  const u32 base = delta == 1 ? BWD_FOLD_WEIGHT_BASE_D1 : delta == 2 ? BWD_FOLD_WEIGHT_BASE_D2 : BWD_FOLD_WEIGHT_BASE_D3;
  const u32 q = slot - base + 1;
  if (delta > round) {
    fold_weights[slot] = F::ZERO();
    return;
  }
  const F one = F::ONE();
  F weight = one;
  for (u32 j = 0; j < delta; ++j) {
    const F challenge = point(round - delta + j);
    weight = F::mul(weight, ((q >> j) & 1) != 0 ? challenge : F::sub(one, challenge));
  }
  fold_weights[slot] = weight;
}
} // namespace airbender::gkr
