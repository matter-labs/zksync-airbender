#pragma once

// Tile / thread tunables for the two-pass and three-pass NTT kernels, shared
// across the forward, hypercube, and monomials-to-evals variants. Each phase
// has its own namespace; bring it into a kernel with `using namespace`.
//
// TODO: make some of these kernel arguments.

namespace airbender::ntt::pass_config {

// Two-pass phase A: first / last 10-stage tile-exchange kernel.
namespace two_pass_phase_a {
constexpr int VALS_PER_THREAD = 32;
constexpr int LOG_DATA_TILE_SIZE = 4;
constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
constexpr int LOG_DATA_TILES_PER_BLOCK = 10;
constexpr int THREAD_TILES_PER_BLOCK = 32;
constexpr int TILE_GMEM_STRIDE = 1 << (24 - LOG_DATA_TILES_PER_BLOCK);
constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;
} // namespace two_pass_phase_a

// Two-pass phase B: 9-stage tile-exchange kernel.
namespace two_pass_phase_b {
constexpr int VALS_PER_THREAD = 32;
constexpr int LOG_DATA_TILE_SIZE = 5;
constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
constexpr int LOG_DATA_TILES_PER_BLOCK = 9;
constexpr int THREAD_TILES_PER_BLOCK = 16;
constexpr int TILE_GMEM_STRIDE = 1 << (23 - LOG_DATA_TILES_PER_BLOCK);
constexpr int IL_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;
} // namespace two_pass_phase_b

// Two-pass phase C: 14-stage warp-exchange kernel.
namespace two_pass_phase_c {
constexpr int WARP_SIZE = 32;
constexpr int VALS_PER_THREAD = 32;
constexpr int WARPS_PER_BLOCK = 16;
constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 16384
} // namespace two_pass_phase_c

// Pipeline prefetch parameters used by the forward and hypercube two-pass
// phase-A and phase-B kernels. Not used by monomials-to-evals (no prefetch).
namespace pipeline_prefetch {
constexpr int PL_GROUP_SIZE = 4;
constexpr int PL_STRIDE = 8;
} // namespace pipeline_prefetch

// Three-pass phase A: 8-stage non-initial/non-final tile-exchange kernel.
namespace three_pass_phase_a {
constexpr int VALS_PER_THREAD = 16;
constexpr int LOG_DATA_TILE_SIZE = 5;
constexpr int TILE_SIZE = 1 << LOG_DATA_TILE_SIZE;
constexpr int LOG_DATA_TILES_PER_BLOCK = 8;
constexpr int THREAD_TILES_PER_BLOCK = 16;
} // namespace three_pass_phase_a

// Three-pass phase B: up-to-8-stage final / initial warp-exchange kernel.
// The derived `INITIAL_EXCHG_REGIONS_PER_WARP` / `OUTPUT_EXCHG_REGIONS_PER_WARP`
// values depend on the `STAGES` template parameter and stay local to each
// kernel body.
namespace three_pass_phase_b {
constexpr int WARP_SIZE = 32;
constexpr int VALS_PER_THREAD = 32;
constexpr int VALS_PER_WARP = WARP_SIZE * VALS_PER_THREAD;
constexpr int WARPS_PER_BLOCK = 8;
constexpr int VALS_PER_BLOCK = WARPS_PER_BLOCK * WARP_SIZE * VALS_PER_THREAD; // 8192
} // namespace three_pass_phase_b

} // namespace airbender::ntt::pass_config
