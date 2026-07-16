// Warp-partial backward continuation kernel, round 1.
//
// Mirrors `round1_flat_warp_split.cu` but replaces the per-row store
// epilogue (`flat_store_unified_contributions`) with a warp-reduce partial
// emitter that collapses the 32 gids in each block into a single (c0, c1)
// pair. Eq is inlined per row before the reduce.

#include "continuation.cuh"

namespace airbender::prover::gkr::backward {

EXTERN __launch_bounds__(128, 8) __global__
    void ab_gkr_main_round1_flat_constant_compact_unified_compact_warp_partial_e4_kernel(const __grid_constant__ flat_round1_unified_desc_compact desc,
                                                                                         const unsigned fold_stride, const unsigned next_layer_size,
                                                                                         const e4 *eq_low, const __grid_constant__ gkr_eq_sizes eq_sizes,
                                                                                         e4 *partials, const unsigned acc_size) {
  constexpr unsigned NUM_WARPS = 4;
  const unsigned lane = threadIdx.x % 32;
  const unsigned warp_id = threadIdx.x / 32;
  const unsigned gid = blockIdx.x * 32 + lane;
  if (gid >= acc_size)
    return;

  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();
  flat_round1_accumulate_unified_compact<e4, NUM_WARPS>(desc, coeff_loader_constant_indexed{}, term_tables_inline<flat_round1_unified_desc_compact>{desc},
                                                        fold_stride, next_layer_size, gid, warp_id, c0, c1);

  __shared__ e4 smem[NUM_WARPS - 1][32];
  flat_store_unified_partials_warp_reduce<e4, NUM_WARPS>(smem, eq_low, eq_sizes, partials, gid, lane, warp_id, c0, c1);
}

// Device-pointer coefficient variant of the round 1 warp-partial kernel.
// Identical algebra; coefficients read from the `coefficients` device buffer
// instead of the `ab_gkr_flat_coefficients` __constant__ symbol.
EXTERN __launch_bounds__(128, 8) __global__ void ab_gkr_main_round1_flat_devptr_compact_unified_compact_warp_partial_e4_kernel(
    const __grid_constant__ flat_round1_unified_desc_compact desc, const unsigned fold_stride, const unsigned next_layer_size, const e4 *coefficients,
    const e4 *eq_low, const __grid_constant__ gkr_eq_sizes eq_sizes, e4 *partials, const unsigned acc_size) {
  constexpr unsigned NUM_WARPS = 4;
  const unsigned lane = threadIdx.x % 32;
  const unsigned warp_id = threadIdx.x / 32;
  const unsigned gid = blockIdx.x * 32 + lane;
  if (gid >= acc_size)
    return;

  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();
  flat_round1_accumulate_unified_compact<e4, NUM_WARPS>(desc, coeff_loader_ptr_indexed{coefficients},
                                                        term_tables_inline<flat_round1_unified_desc_compact>{desc}, fold_stride, next_layer_size, gid, warp_id,
                                                        c0, c1);

  __shared__ e4 smem[NUM_WARPS - 1][32];
  flat_store_unified_partials_warp_reduce<e4, NUM_WARPS>(smem, eq_low, eq_sizes, partials, gid, lane, warp_id, c0, c1);
}

// Device-pointer TERMS variant of the round 1 warp-partial kernel. Terms/tiles
// and coefficients both live in device memory (`flat_term_tables` +
// `coefficients`); the `_devptr` descriptor carries only the small fields.
// Selected on inline-desc overflow.
EXTERN __launch_bounds__(128, 8) __global__ void ab_gkr_main_round1_flat_devptr_terms_compact_unified_compact_warp_partial_e4_kernel(
    const __grid_constant__ flat_round1_unified_desc_compact_devptr desc, const unsigned fold_stride, const unsigned next_layer_size, const e4 *coefficients,
    const flat_term_tables term_tables, const e4 *eq_low, const __grid_constant__ gkr_eq_sizes eq_sizes, e4 *partials, const unsigned acc_size) {
  constexpr unsigned NUM_WARPS = 4;
  const unsigned lane = threadIdx.x % 32;
  const unsigned warp_id = threadIdx.x / 32;
  const unsigned gid = blockIdx.x * 32 + lane;
  if (gid >= acc_size)
    return;

  e4 c0 = e4::ZERO();
  e4 c1 = e4::ZERO();
  flat_round1_accumulate_unified_compact<e4, NUM_WARPS>(desc, coeff_loader_ptr_indexed{coefficients}, term_tables_devptr{term_tables}, fold_stride,
                                                        next_layer_size, gid, warp_id, c0, c1);

  __shared__ e4 smem[NUM_WARPS - 1][32];
  flat_store_unified_partials_warp_reduce<e4, NUM_WARPS>(smem, eq_low, eq_sizes, partials, gid, lane, warp_id, c0, c1);
}

} // namespace airbender::prover::gkr::backward
