#pragma once

#include "gkr/support/descriptors.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_MAIN_TAIL_BLOCK_THREADS = 256;

template <typename F> DEVICE_FORCEINLINE F bwd_main_tail_eq_weight(const bool bit, const F coordinate) {
  return bit ? coordinate : F::sub(F::ONE(), coordinate);
}

template <typename Descriptor, typename F> DEVICE_FORCEINLINE void bwd_main_tail_build_d3_weights(const Descriptor &desc, F (&weights)[7]) {
  if (threadIdx.x < 7) {
    const u32 q = threadIdx.x + 1;
    F weight = F::ONE();
#pragma unroll
    for (u32 bit = 0; bit < 3; ++bit) {
      const F coordinate = desc.challenges_out[u32{desc.tail_start} - 3u + bit];
      weight = F::mul(weight, bwd_main_tail_eq_weight(((q >> bit) & 1u) != 0, coordinate));
    }
    weights[threadIdx.x] = weight;
  }
}

template <typename Descriptor, typename F>
DEVICE_FORCEINLINE void bwd_main_tail_fold_d1(const Descriptor &desc, const F *input, const u32 input_stride, F *output, const u32 output_stride,
                                              const F challenge) {
  const u32 total = u32{desc.source_count} * output_stride;
  for (u32 flat = threadIdx.x; flat < total; flat += BWD_MAIN_TAIL_BLOCK_THREADS) {
    const u32 source = flat / output_stride;
    const u32 row = flat - source * output_stride;
    const F *pair = input + static_cast<size_t>(source) * input_stride + 2u * row;
    output[static_cast<size_t>(source) * output_stride + row] = F::fma(F::sub(pair[1], pair[0]), challenge, pair[0]);
  }
}

} // namespace airbender::gkr::backward
