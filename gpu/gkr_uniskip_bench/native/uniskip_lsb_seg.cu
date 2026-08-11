#include "uniskip_lsb_seg.cuh"

namespace airbender::gkr_uniskip_bench {

// CARRIER S: the slab is dynamic shared memory, so the carveout is a launch property and
// two symbols with ONE body are what separates the two carveout requests. The reduction
// plane aliases the slab's head, which the cache-retire barrier makes safe.
EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_seg_s_cv64_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan,
                                              const __grid_constant__ uniskip_seg_desc seg) {
  extern __shared__ __align__(16) u32 seg_slab[];
  const uniskip_seg_carrier_smem car{seg_slab};
  uniskip_seg_body<uniskip_seg_carrier_smem, false>(desc, plan, seg, car, reinterpret_cast<e4 *>(seg_slab));
}

// The sticky-carveout clone: same body, second symbol. `cudaFuncSetAttribute` is per
// function and sticky for the process, so a rotation between two carveouts needs two
// entry points rather than a reset between launches.
EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_seg_s_cv100_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan,
                                               const __grid_constant__ uniskip_seg_desc seg) {
  extern __shared__ __align__(16) u32 seg_slab[];
  const uniskip_seg_carrier_smem car{seg_slab};
  uniskip_seg_body<uniskip_seg_carrier_smem, false>(desc, plan, seg, car, reinterpret_cast<e4 *>(seg_slab));
}

EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_seg_s_acc_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan,
                                             const __grid_constant__ uniskip_seg_desc seg) {
  extern __shared__ __align__(16) u32 seg_slab[];
  const uniskip_seg_carrier_smem car{seg_slab};
  uniskip_seg_body<uniskip_seg_carrier_smem, false, true>(desc, plan, seg, car, reinterpret_cast<e4 *>(seg_slab));
}

// CARRIER G: the slab is a per-block region of device scratch, so the carveout is no longer
// a launch property and the reduction plane goes back to being static shared. One symbol is
// enough - what a rotation would steer here is the L2 residency of the slab, not a partition.
EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_seg_g_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan,
                                         const __grid_constant__ uniskip_seg_desc seg) {
  __shared__ e4 plane[UNISKIP_SEG_K * UNISKIP_CELLS];
  const uniskip_seg_carrier_gmem car{reinterpret_cast<u32 *>(seg.slab_base) + blockIdx.x * seg.slab_stride_words};
  uniskip_seg_body<uniskip_seg_carrier_gmem, false>(desc, plan, seg, car, plane);
}

// The MACHINERY FLOOR: no slab, no prologue, no fill-release barrier. Every reference takes
// the recompute leg because the uploaded records carry the sentinel, which is what makes
// this the seg cohort loop's own price rather than a second body.
EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_seg_recompute_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_seg_desc seg) {
  __shared__ e4 plane[UNISKIP_SEG_K * UNISKIP_CELLS];
  const uniskip_seg_carrier_smem car{reinterpret_cast<u32 *>(plane)};
  uniskip_cache_desc unread_plan;
  uniskip_seg_body<uniskip_seg_carrier_smem, true>(desc, unread_plan, seg, car, plane);
}

EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_segb_g_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan,
                                          const __grid_constant__ uniskip_seg_desc seg) {
  const uniskip_seg_carrier_gmem car{reinterpret_cast<u32 *>(seg.slab_base) + blockIdx.x * seg.slab_stride_words};
  uniskip_segb_body<uniskip_seg_carrier_gmem, false>(desc, plan, seg, car);
}

EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_segb_g_slotted_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_cache_desc plan,
                                                  const __grid_constant__ uniskip_seg_desc seg, u32 *mask) {
  __shared__ u32 published;
  if (threadIdx.x == 0)
    published = uniskip_slot_claim(mask);
  __syncthreads(); // claim-publish
  const u32 region = published;
  const uniskip_seg_carrier_gmem car{reinterpret_cast<u32 *>(seg.slab_base) + region * seg.slab_stride_words};
  uniskip_segb_body<uniskip_seg_carrier_gmem, false>(desc, plan, seg, car);
  __syncthreads(); // pre-release: every block-local slab read has retired
  if (threadIdx.x == 0)
    uniskip_slot_release(mask, region);
}

EXTERN __global__ void __launch_bounds__(UNISKIP_PAIR_WARPS_128 * 32, 7)
    ab_gkr_uniskip_eval_lsb_segb_recompute_kernel(const __grid_constant__ uniskip_pair_desc desc, const __grid_constant__ uniskip_seg_desc seg) {
  const uniskip_seg_carrier_gmem car{reinterpret_cast<u32 *>(seg.slab_base) + blockIdx.x * seg.slab_stride_words};
  uniskip_cache_desc unread_plan;
  uniskip_segb_body<uniskip_seg_carrier_gmem, true>(desc, unread_plan, seg, car);
}

} // namespace airbender::gkr_uniskip_bench
