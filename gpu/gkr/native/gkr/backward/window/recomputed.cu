// MAIN R0 window kernels with recomputed endpoints: the four production entries.
//
// One block of 288 threads (nine selector warps, one 32-row tile) per launch row tile; the
// descriptor is passed by value with an 8192-word program plus the scalar seed. The runtime picks
// one entry per layer from the program alone (src/backward/window): b4 when the BF section holds
// more than four times the E4 records, else b3; among b4 the unit body when the shape is a subset
// of 0x771, the tails body when the linear-tails lowering set BF_LINEAR_TAIL, else the packed body.
// The runtime asserts the program's shape mask is a subset of the entry's shape before launching.
//
#include "recomputed.cuh"

namespace {
using airbender::gkr::backward::BWD_WINDOW_BLOCK_THREADS;
using airbender::gkr::backward::recomputed::bwd_window_desc;
using airbender::gkr::backward::recomputed::bwd_window_execute;
} // namespace

// Twelve 96-bit outer accumulators with a three-block launch bound.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 3) void ab_gkr_r0_recomputed_b3(const __grid_constant__ bwd_window_desc desc,
                                                                                              const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x7f7, false, false, false, false, false>(desc, scalar_seed);
}

// Packed outer accumulators with a four-block launch bound for BF-heavy layers whose shape fits neither
// the unit nor the tails body.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_recomputed_packed_b4(const __grid_constant__ bwd_window_desc desc,
                                                                                                     const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x7f7, true, false, false, false, false>(desc, scalar_seed);
}

// Unit-factor shape (no banked immediates, no inner reduction cadence, no negative BF factors, no
// linear tails): every group has at least two products and linear singletons feed two cells.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_recomputed_unit_b4(const __grid_constant__ bwd_window_desc desc,
                                                                                                   const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x771, true, true, true, true, true>(desc, scalar_seed);
}

// Linear-tails lowering: groups carry a product prefix and a linear tail walked by the tail loop.
EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 4) void ab_gkr_r0_recomputed_tails_b4(const __grid_constant__ bwd_window_desc desc,
                                                                                                    const u32 scalar_seed) {
  if (blockDim.x != BWD_WINDOW_BLOCK_THREADS)
    return;
  bwd_window_execute<0x7ff, true, true, false, false, true>(desc, scalar_seed);
}
