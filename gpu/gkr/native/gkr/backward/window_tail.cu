// Tensor round tail: the three MAIN or DR sumcheck rounds a width-3 window
// replaces. `partials` is the window executor's row-tile-major
// `27 * row_tiles` matrix (`bwd_window_publish`); the reduced 27-cell tensor is
// indexed `9 * a0 + 3 * a1 + a2` over `{0, 1, infinity}`, axis `r` being the
// variable round `r` binds.

#include "tail_common.cuh"
#include "window/window_source.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS = 256;
constexpr u32 BWD_WINDOW_TAIL_BLOCK_THREADS = 256;

static_assert(BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS % BWD_WINDOW_WARP_LANES == 0, "the split reduce block must be whole warps");

DEVICE_FORCEINLINE e4 bwd_window_tail_eq_weight(const bool bit, const e4 coordinate) { return bit ? coordinate : e4::sub(e4::ONE(), coordinate); }

// f(0) + z (f(1) - f(0)) + z (z - 1) f(infinity): the `{0, 1, infinity}`
// collapse of one axis at the round's challenge.
DEVICE_FORCEINLINE e4 bwd_window_tail_bind(const e4 at_zero, const e4 at_one, const e4 leading, const e4 challenge) {
  const e4 linear = e4::mul(e4::sub(e4::sub(at_one, leading), at_zero), challenge);
  const e4 quadratic = e4::mul(e4::mul(leading, challenge), challenge);
  return e4::add(e4::add(at_zero, linear), quadratic);
}

DEVICE_FORCEINLINE void bwd_window_tail_rounds(const e4 *tensor, const e4 *prev_coords, u32 *seed, e4 *claim, e4 *eq, e4 *coeffs, e4 *challenges, e4 *active_eq,
                                               const u32 eq_bits) {
  __shared__ e4 rho[3], bound9[9], bound3[3], challenge, inverse[2];
  const u32 lane = threadIdx.x;
  if (lane < 32) {
    // Callers may alias prev_coords with challenges.
    // Snapshot all three coordinates before the first challenge store.
    if (lane < 3)
      rho[lane] = prev_coords[lane];
    __syncwarp();
#pragma unroll 1
    for (u32 round = 0; round < 3; ++round) {
      e4 e = e4::ZERO(), c = e4::ZERO();
      if (round == 0 && lane < 4) {
        const u32 i = 3 * (lane >> 1) + (lane & 1);
        const e4 weight = e4::mul(bwd_window_tail_eq_weight((lane >> 1) != 0, rho[1]), bwd_window_tail_eq_weight((lane & 1) != 0, rho[2]));
        e = e4::mul(tensor[i], weight);
        c = e4::mul(tensor[18 + i], weight);
      } else if (round == 1 && lane < 2) {
        const e4 weight = bwd_window_tail_eq_weight(lane != 0, rho[2]);
        e = e4::mul(bound9[lane], weight);
        c = e4::mul(bound9[6 + lane], weight);
      } else if (round == 2 && lane == 0) {
        e = bound3[0];
        c = bound3[2];
      }
      e = gkr_trace_holder_partials_warp_reduce_sum(e);
      c = gkr_trace_holder_partials_warp_reduce_sum(c);
      // inv(0) is zero; reconverge before consuming either lane result.
      if (lane < 2)
        inverse[lane] = e4::inv(lane == 0 ? *eq : rho[round]);
      __syncwarp();
      if (lane == 0) {
        const e4 r = run_round_update_with_inverses(e, c, rho[round], inverse[0], inverse[1], seed, claim, eq, coeffs + 4 * round);
        challenge = r;
        challenges[round] = r;
      }
      __syncwarp();
      if (round == 0 && lane < 9)
        bound9[lane] = bwd_window_tail_bind(tensor[lane], tensor[9 + lane], tensor[18 + lane], challenge);
      else if (round == 1 && lane < 3)
        bound3[lane] = bwd_window_tail_bind(bound9[lane], bound9[3 + lane], bound9[6 + lane], challenge);
      __syncwarp();
    }
  }
  // Every thread participates, including the seven warps idle during rounds.
  fold_active_eq_slot<BWD_WINDOW_TAIL_BLOCK_THREADS>(active_eq, eq_bits);
}

// One block per tensor cell reduces that cell's column of the partial matrix.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS) void ab_gkr_bwd_window3_tail_reduce_kernel(const e4 *__restrict__ partials,
                                                                                                                     const u32 row_tiles,
                                                                                                                     e4 *__restrict__ tensor_out) {
  constexpr u32 WARPS = BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS / BWD_WINDOW_WARP_LANES;
  __shared__ e4 warp_sums[WARPS];
  const u32 cell = blockIdx.x;
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;

  e4 sum = e4::ZERO();
  for (u32 row_tile = threadIdx.x; row_tile < row_tiles; row_tile += BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS)
    sum = e4::add(sum, partials[static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + cell]);
  sum = gkr_trace_holder_partials_warp_reduce_sum(sum);
  if (lane == 0)
    warp_sums[warp] = sum;
  __syncthreads();
  if (warp != 0)
    return;
  sum = gkr_trace_holder_partials_warp_reduce_sum(lane < WARPS ? warp_sums[lane] : e4::ZERO());
  if (lane == 0)
    tensor_out[cell] = sum;
}

// Play the three rounds from the reduced tensor.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_TAIL_BLOCK_THREADS) void ab_gkr_bwd_window3_tail_from_tensor_kernel(
    const e4 *__restrict__ tensor, const e4 *prev_claim_coords, u32 *__restrict__ seed_io, e4 *__restrict__ claim_io, e4 *__restrict__ eq_prefactor_io,
    e4 *__restrict__ coeffs_out, e4 *challenges_out, e4 *__restrict__ active_eq_slot_base, const u32 active_eq_size_before_fold) {
  bwd_window_tail_rounds(tensor, prev_claim_coords, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenges_out, active_eq_slot_base,
                         active_eq_size_before_fold);
}

} // namespace airbender::gkr::backward
