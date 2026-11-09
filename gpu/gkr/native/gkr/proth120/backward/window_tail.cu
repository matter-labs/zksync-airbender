#include "../../support/kernel_helpers.cuh"
#include "tail_common_pr.cuh"

namespace airbender::gkr::proth120::backward {

constexpr u32 PR_WINDOW_TAIL_TENSOR_CELLS = 27;
constexpr u32 PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS = 256;
constexpr u32 PR_WINDOW_TAIL_BLOCK_THREADS = 256;
constexpr u32 PR_WINDOW_TAIL_WARP_LANES = 32;

static_assert(PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS % PR_WINDOW_TAIL_WARP_LANES == 0);
static_assert(sizeof(void *) == 8 && sizeof(pr) == 16 && alignof(pr) == 16);
static_assert(8 * sizeof(void *) + sizeof(u32) <= 32764);

DEVICE_FORCEINLINE pr pr_window_tail_eq_weight(const bool bit, const pr coordinate) { return bit ? coordinate : pr::sub(pr::ONE(), coordinate); }

DEVICE_FORCEINLINE pr pr_window_tail_bind(const pr at_zero, const pr at_one, const pr leading, const pr challenge) {
  const pr linear = pr::mul(pr::sub(pr::sub(at_one, leading), at_zero), challenge);
  const pr quadratic = pr::mul(pr::mul(leading, challenge), challenge);
  return pr::add(pr::add(at_zero, linear), quadratic);
}

EXTERN __global__ __launch_bounds__(PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS) void ab_pr_gkr_window_tail_reduce_kernel(const pr *__restrict__ partials,
                                                                                                                  const u32 row_tiles,
                                                                                                                  pr *__restrict__ tensor_out) {
  constexpr u32 WARPS = PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS / PR_WINDOW_TAIL_WARP_LANES;
  __shared__ pr warp_sums[WARPS];
  if (blockDim.x != PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS || blockIdx.x >= PR_WINDOW_TAIL_TENSOR_CELLS)
    return;
  const u32 cell = blockIdx.x;
  const u32 lane = threadIdx.x % PR_WINDOW_TAIL_WARP_LANES;
  const u32 warp = threadIdx.x / PR_WINDOW_TAIL_WARP_LANES;
  pr sum = pr::ZERO();
  for (u32 row_tile = threadIdx.x; row_tile < row_tiles; row_tile += PR_WINDOW_TAIL_REDUCE_BLOCK_THREADS)
    sum = pr::add(sum, partials[static_cast<size_t>(row_tile) * PR_WINDOW_TAIL_TENSOR_CELLS + cell]);
  sum = gkr_trace_holder_partials_warp_reduce_sum(sum);
  if (lane == 0)
    warp_sums[warp] = sum;
  __syncthreads();
  if (warp != 0)
    return;
  sum = gkr_trace_holder_partials_warp_reduce_sum(lane < WARPS ? warp_sums[lane] : pr::ZERO());
  if (lane == 0)
    tensor_out[cell] = sum;
}

EXTERN __global__ __launch_bounds__(PR_WINDOW_TAIL_BLOCK_THREADS) void ab_pr_gkr_window_tail_kernel(
    const pr *__restrict__ tensor, const pr *prev_claim_coords, u8 *__restrict__ seed_io, pr *__restrict__ claim_io, pr *__restrict__ eq_prefactor_io,
    pr *__restrict__ coeffs_out, pr *challenges_out, pr *__restrict__ active_eq_slot_base, const u32 active_eq_size_before_fold) {
  __shared__ pr rho[3];
  __shared__ pr bound9[9];
  __shared__ pr bound3[3];
  __shared__ pr challenge;
  __shared__ pr inverse[2];
  if (blockDim.x != PR_WINDOW_TAIL_BLOCK_THREADS || gridDim.x != 1)
    return;
  const u32 lane = threadIdx.x;
  if (lane < PR_WINDOW_TAIL_WARP_LANES) {
    if (lane < 3)
      rho[lane] = prev_claim_coords[lane];
    __syncwarp();
#pragma unroll 1
    for (u32 round = 0; round < 3; ++round) {
      pr e = pr::ZERO();
      pr c = pr::ZERO();
      if (round == 0 && lane < 4) {
        const u32 i = 3 * (lane >> 1) + (lane & 1);
        const pr weight = pr::mul(pr_window_tail_eq_weight((lane >> 1) != 0, rho[1]), pr_window_tail_eq_weight((lane & 1) != 0, rho[2]));
        e = pr::mul(tensor[i], weight);
        c = pr::mul(tensor[18 + i], weight);
      } else if (round == 1 && lane < 2) {
        const pr weight = pr_window_tail_eq_weight(lane != 0, rho[2]);
        e = pr::mul(bound9[lane], weight);
        c = pr::mul(bound9[6 + lane], weight);
      } else if (round == 2 && lane == 0) {
        e = bound3[0];
        c = bound3[2];
      }
      e = gkr_trace_holder_partials_warp_reduce_sum(e);
      c = gkr_trace_holder_partials_warp_reduce_sum(c);
      if (lane < 2)
        inverse[lane] = pr::inv(lane == 0 ? *eq_prefactor_io : rho[round]);
      __syncwarp();
      if (lane == 0) {
        const pr r = run_round_update_with_inverses_pr(e, c, rho[round], inverse[0], inverse[1], seed_io, claim_io, eq_prefactor_io, coeffs_out + 4 * round);
        challenge = r;
        challenges_out[round] = r;
      }
      __syncwarp();
      if (round == 0 && lane < 9)
        bound9[lane] = pr_window_tail_bind(tensor[lane], tensor[9 + lane], tensor[18 + lane], challenge);
      else if (round == 1 && lane < 3)
        bound3[lane] = pr_window_tail_bind(bound9[lane], bound9[3 + lane], bound9[6 + lane], challenge);
      __syncwarp();
    }
  }
  fold_active_eq_slot_pr<PR_WINDOW_TAIL_BLOCK_THREADS>(active_eq_slot_base, active_eq_size_before_fold);
}

} // namespace airbender::gkr::proth120::backward
