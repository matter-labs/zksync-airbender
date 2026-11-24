#pragma once

#include "gkr/forward/fwd_vm.cuh"
#include "gkr/support/lookup_helpers.cuh"

namespace airbender::gkr {

template <typename Pair, typename F> DEVICE_FORCEINLINE void fused_reduction_round0(const Pair &pair, F *smem, const u32 tile) {
  constexpr u32 round_len = 64;
  const u32 lane = threadIdx.x & (warpSize - 1);
  const u32 block_input = tile * 128;
  const u32 block_output = tile * round_len;

#pragma unroll
  for (u32 local = lane; local < round_len; local += warpSize) {
    const u32 even = block_input + 2 * local;
    const u32 odd = even + 1;
    F out0;
    F out1;
    if (pair.kind == FWD_VM_REDUCTION_PAIR_PAIRWISE2) {
      gkr_eval_product(load<F, ld_modifier::ca>(pair.input[0], even), load<F, ld_modifier::ca>(pair.input[0], odd), out0);
      gkr_eval_product(load<F, ld_modifier::ca>(pair.input[1], even), load<F, ld_modifier::ca>(pair.input[1], odd), out1);
    } else {
      const F a = load<F, ld_modifier::ca>(pair.input[0], even);
      const F b = load<F, ld_modifier::ca>(pair.input[1], even);
      const F c = load<F, ld_modifier::ca>(pair.input[0], odd);
      const F d = load<F, ld_modifier::ca>(pair.input[1], odd);
      gkr_eval_lookup_pair(a, b, c, d, out0, out1);
    }
    smem[local] = out0;
    smem[round_len + local] = out1;
    store<F, st_modifier::cs>(pair.round_outputs[0][0], out0, block_output + local);
    store<F, st_modifier::cs>(pair.round_outputs[0][1], out1, block_output + local);
  }
  // Round 1 reads values written by other lanes.
  __syncwarp();
}

template <typename Pair, typename F> DEVICE_FORCEINLINE void fused_reduction_pair(const Pair &pair, F *smem, const u32 tile) {
  fused_reduction_round0(pair, smem, tile);
  const u32 lane = threadIdx.x & (warpSize - 1);

#pragma unroll
  for (u32 round = 1; round < FWD_VM_FUSED_REDUCTION_ROUNDS; round++) {
    const u32 round_len = 64 >> round;
    F out0;
    F out1;
    if (lane < round_len) {
      if (pair.kind == FWD_VM_REDUCTION_PAIR_PAIRWISE2) {
        gkr_eval_product(smem[2 * lane], smem[2 * lane + 1], out0);
        gkr_eval_product(smem[64 + 2 * lane], smem[64 + 2 * lane + 1], out1);
      } else {
        gkr_eval_lookup_pair(smem[2 * lane], smem[64 + 2 * lane], smem[2 * lane + 1], smem[64 + 2 * lane + 1], out0, out1);
      }
    }
    // Finish all reads before overwriting inputs, then publish writes before the next round.
    __syncwarp();
    if (lane < round_len) {
      smem[lane] = out0;
      smem[64 + lane] = out1;
      const u32 output = tile * round_len + lane;
      store<F, st_modifier::cs>(pair.round_outputs[round][0], out0, output);
      store<F, st_modifier::cs>(pair.round_outputs[round][1], out1, output);
    }
    __syncwarp();
  }
}

} // namespace airbender::gkr
