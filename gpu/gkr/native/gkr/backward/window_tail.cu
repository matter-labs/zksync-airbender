// Tensor round tail: the three main-layer sumcheck rounds a width-3 window
// replaces. `partials` is the window executor's row-tile-major
// `27 * row_tiles` matrix (`bwd_window_publish`); the reduced 27-cell tensor is
// indexed `9 * a0 + 3 * a1 + a2` over `{0, 1, infinity}`, axis `r` being the
// variable round `r` binds.
//
// Two reduction arms, identical semantics: the absorbed arm reduces the matrix
// and plays the rounds in one block, the split arm reduces in 27 blocks and
// plays the rounds from the reduced tensor.

#include "mega_finalize.cuh"
#include "window/window_source.cuh"

namespace airbender::gkr::backward {

using ::airbender::gkr::fold_active_eq_slot;
using ::airbender::gkr::ops::run_round_update_single_thread;

// Row-tile slots the absorbed arm reduces in parallel, one channel per tensor
// cell. Consecutive threads read consecutive cells of one row tile.
constexpr u32 BWD_WINDOW_TAIL_TILE_SLOTS = 32;
constexpr u32 BWD_WINDOW_TAIL_ABSORBED_BLOCK_THREADS = BWD_WINDOW_TENSOR_CELLS * BWD_WINDOW_TAIL_TILE_SLOTS;
constexpr u32 BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS = 256;
constexpr u32 BWD_WINDOW_TAIL_BLOCK_THREADS = 256;

static_assert(BWD_WINDOW_TAIL_ABSORBED_BLOCK_THREADS == 864, "absorbed tail block geometry drift");
static_assert(BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS % BWD_SEG_WARP_LANES == 0, "the split reduce block must be whole warps");

DEVICE_FORCEINLINE e4 bwd_window_tail_eq_weight(const bool bit, const e4 coordinate) { return bit ? coordinate : e4::sub(e4::ONE(), coordinate); }

// f(0) + z (f(1) - f(0)) + z (z - 1) f(infinity): the `{0, 1, infinity}`
// collapse of one axis at the round's challenge.
DEVICE_FORCEINLINE e4 bwd_window_tail_bind(const e4 at_zero, const e4 at_one, const e4 leading, const e4 challenge) {
  const e4 linear = e4::mul(e4::sub(e4::sub(at_one, leading), at_zero), challenge);
  const e4 quadratic = e4::mul(e4::mul(leading, challenge), challenge);
  return e4::add(e4::add(at_zero, linear), quadratic);
}

// Mirror of `backward::window::reference::tensor_round_tail_reference`, run by
// one thread. The rounds are sequential: each collapse needs the challenge the
// previous round's transcript drew.
//
// `prev_claim_coords` and `challenges_out` are NOT restrict-qualified: the
// per-layer schedulers build the output claim-point view over the same symbol
// the input view reads, so the three coordinates are read into registers
// before the first challenge store overwrites them.
DEVICE_FORCEINLINE void bwd_window_tail_rounds(const e4 *tensor, const e4 *prev_claim_coords, u32 *__restrict__ seed_io, e4 *__restrict__ claim_io,
                                               e4 *__restrict__ eq_prefactor_io, e4 *__restrict__ coeffs_out, e4 *challenges_out) {
  const e4 rho0 = prev_claim_coords[0];
  const e4 rho1 = prev_claim_coords[1];
  const e4 rho2 = prev_claim_coords[2];

  e4 pair_weights[4];
#pragma unroll
  for (u32 index = 0; index < 4; ++index)
    pair_weights[index] = e4::mul(bwd_window_tail_eq_weight((index >> 1) != 0, rho1), bwd_window_tail_eq_weight((index & 1) != 0, rho2));
  e4 single_weights[2];
#pragma unroll
  for (u32 index = 0; index < 2; ++index)
    single_weights[index] = bwd_window_tail_eq_weight(index != 0, rho2);

  e4 e_partial = e4::ZERO();
  e4 c_partial = e4::ZERO();
#pragma unroll
  for (u32 x1 = 0; x1 < 2; ++x1)
#pragma unroll
    for (u32 x2 = 0; x2 < 2; ++x2) {
      const e4 weight = pair_weights[2 * x1 + x2];
      e_partial = e4::add(e_partial, e4::mul(tensor[3 * x1 + x2], weight));
      c_partial = e4::add(c_partial, e4::mul(tensor[18 + 3 * x1 + x2], weight));
    }

  e4 challenge;
  run_round_update_single_thread(e_partial, c_partial, rho0, seed_io, claim_io, eq_prefactor_io, coeffs_out, &challenge);
  challenges_out[0] = challenge;

  e4 bound_nine[9];
#pragma unroll
  for (u32 index = 0; index < 9; ++index)
    bound_nine[index] = bwd_window_tail_bind(tensor[index], tensor[9 + index], tensor[18 + index], challenge);

  e_partial = e4::ZERO();
  c_partial = e4::ZERO();
#pragma unroll
  for (u32 x2 = 0; x2 < 2; ++x2) {
    e_partial = e4::add(e_partial, e4::mul(bound_nine[x2], single_weights[x2]));
    c_partial = e4::add(c_partial, e4::mul(bound_nine[6 + x2], single_weights[x2]));
  }

  run_round_update_single_thread(e_partial, c_partial, rho1, seed_io, claim_io, eq_prefactor_io, coeffs_out + 4, &challenge);
  challenges_out[1] = challenge;

  e4 bound_three[3];
#pragma unroll
  for (u32 index = 0; index < 3; ++index)
    bound_three[index] = bwd_window_tail_bind(bound_nine[index], bound_nine[3 + index], bound_nine[6 + index], challenge);

  run_round_update_single_thread(bound_three[0], bound_three[2], rho2, seed_io, claim_io, eq_prefactor_io, coeffs_out + 8, &challenge);
  challenges_out[2] = challenge;
}

// Absorbed arm: one block reduces the whole partial matrix and plays the three
// rounds. Thread `t * 27 + c` accumulates cell `c` of every row tile congruent
// to `t`.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_TAIL_ABSORBED_BLOCK_THREADS) void ab_gkr_bwd_window3_tail_absorbed_kernel(
    const e4 *__restrict__ partials, const u32 row_tiles, const e4 *prev_claim_coords, u32 *__restrict__ seed_io, e4 *__restrict__ claim_io,
    e4 *__restrict__ eq_prefactor_io, e4 *__restrict__ coeffs_out, e4 *challenges_out, e4 *__restrict__ active_eq_slot_base,
    const u32 active_eq_size_before_fold) {
  constexpr u32 BLOCK = BWD_WINDOW_TAIL_ABSORBED_BLOCK_THREADS;
  __shared__ e4 channels[BLOCK];
  const u32 tid = threadIdx.x;
  const u32 cell = tid % BWD_WINDOW_TENSOR_CELLS;
  const u32 tile_slot = tid / BWD_WINDOW_TENSOR_CELLS;

  e4 sum = e4::ZERO();
  for (u32 row_tile = tile_slot; row_tile < row_tiles; row_tile += BWD_WINDOW_TAIL_TILE_SLOTS)
    sum = e4::add(sum, partials[static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + cell]);
  channels[tid] = sum;
  __syncthreads();

#pragma unroll
  for (u32 stride = BWD_WINDOW_TAIL_TILE_SLOTS / 2; stride > 0; stride >>= 1) {
    if (tile_slot < stride)
      channels[tid] = e4::add(channels[tid], channels[tid + stride * BWD_WINDOW_TENSOR_CELLS]);
    __syncthreads();
  }

  if (tid == 0)
    bwd_window_tail_rounds(channels, prev_claim_coords, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenges_out);

  fold_active_eq_slot<BLOCK>(active_eq_slot_base, active_eq_size_before_fold);
}

// Split arm stage 1: one block per tensor cell, reducing that cell's column of
// the partial matrix. Launched with exactly `BWD_WINDOW_TENSOR_CELLS` blocks.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS) void ab_gkr_bwd_window3_tail_reduce_kernel(const e4 *__restrict__ partials,
                                                                                                                     const u32 row_tiles,
                                                                                                                     e4 *__restrict__ tensor_out) {
  constexpr u32 WARPS = BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS / BWD_SEG_WARP_LANES;
  __shared__ e4 warp_sums[WARPS];
  const u32 cell = blockIdx.x;
  const u32 lane = threadIdx.x & BWD_SEG_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_SEG_WARP_SHIFT;

  e4 sum = e4::ZERO();
  for (u32 row_tile = threadIdx.x; row_tile < row_tiles; row_tile += BWD_WINDOW_TAIL_REDUCE_BLOCK_THREADS)
    sum = e4::add(sum, partials[static_cast<size_t>(row_tile) * BWD_WINDOW_TENSOR_CELLS + cell]);
  sum = bwd_window_warp_sum(sum);
  if (lane == 0)
    warp_sums[warp] = sum;
  __syncthreads();
  if (warp != 0)
    return;
  sum = bwd_window_warp_sum(lane < WARPS ? warp_sums[lane] : e4::ZERO());
  if (lane == 0)
    tensor_out[cell] = sum;
}

// Split arm stage 2: play the three rounds from the reduced tensor.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_TAIL_BLOCK_THREADS) void ab_gkr_bwd_window3_tail_from_tensor_kernel(
    const e4 *__restrict__ tensor, const e4 *prev_claim_coords, u32 *__restrict__ seed_io, e4 *__restrict__ claim_io, e4 *__restrict__ eq_prefactor_io,
    e4 *__restrict__ coeffs_out, e4 *challenges_out, e4 *__restrict__ active_eq_slot_base, const u32 active_eq_size_before_fold) {
  if (threadIdx.x == 0)
    bwd_window_tail_rounds(tensor, prev_claim_coords, seed_io, claim_io, eq_prefactor_io, coeffs_out, challenges_out);

  fold_active_eq_slot<BWD_WINDOW_TAIL_BLOCK_THREADS>(active_eq_slot_base, active_eq_size_before_fold);
}

} // namespace airbender::gkr::backward
