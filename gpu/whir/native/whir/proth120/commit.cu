#include "common.cuh"
#include "keccak256.cuh"
#include "primitives/memory.cuh"
#include "primitives/proth120.cuh"
#include "proth120/context.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using ::airbender::hash::keccak256::digest;
using ::airbender::ntt::ab_pr_convert_leaf;
using ::airbender::ntt::pr_root_power_inv;
using ::airbender::ntt::proth120_twiddle_descriptor;

namespace airbender::whir {

template <u32 LOG_VALUES>
DEVICE_FORCEINLINE void pr_whir_convert_tile_leaves(pr *tile, const u32 log_n, const proth120_twiddle_descriptor &d, const u32 log_domain, const u32 k0,
                                                    const u32 cosets) {
  constexpr u32 VALUES = 1u << LOG_VALUES;
  const u32 log_leaves = log_n - LOG_VALUES;
  const u64 gid = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (gid >= static_cast<u64>(cosets) << log_leaves)
    return;
  const u32 local = static_cast<u32>(gid >> log_leaves);
  const u32 j = static_cast<u32>(gid) & ((1u << log_leaves) - 1u);
  const u64 mask = (u64{1} << d.log_max_domain) - 1;
  const u64 exponent = ((static_cast<u64>(k0 + local) << (d.log_max_domain - log_domain)) + (static_cast<u64>(j) << (d.log_max_domain - log_n))) & mask;
  const pr base_root_inv = pr_root_power_inv(d, exponent);
  pr *coset = tile + (static_cast<u64>(local) << log_n) + j;
  const u32 leaves = 1u << log_leaves;
  pr leaf[VALUES];
#pragma unroll
  for (u32 slot = 0; slot < VALUES; slot++)
    leaf[slot] = load_cg(coset + leaves * bitreverse_low_bits(slot, LOG_VALUES));
  ab_pr_convert_leaf<LOG_VALUES>(d, leaf, base_root_inv);
#pragma unroll
  for (u32 slot = 0; slot < VALUES; slot++)
    store_cg(coset + leaves * bitreverse_low_bits(slot, LOG_VALUES), leaf[slot]);
}

EXTERN __launch_bounds__(256) __global__ void ab_pr_whir_convert_tile_leaves_1_kernel(pr *tile, const u32 log_n, const proth120_twiddle_descriptor d,
                                                                                      const u32 log_domain, const u32 k0, const u32 cosets) {
  pr_whir_convert_tile_leaves<1>(tile, log_n, d, log_domain, k0, cosets);
}

EXTERN __launch_bounds__(256) __global__ void ab_pr_whir_convert_tile_leaves_2_kernel(pr *tile, const u32 log_n, const proth120_twiddle_descriptor d,
                                                                                      const u32 log_domain, const u32 k0, const u32 cosets) {
  pr_whir_convert_tile_leaves<2>(tile, log_n, d, log_domain, k0, cosets);
}

EXTERN __launch_bounds__(256) __global__ void ab_pr_whir_convert_tile_leaves_3_kernel(pr *tile, const u32 log_n, const proth120_twiddle_descriptor d,
                                                                                      const u32 log_domain, const u32 k0, const u32 cosets) {
  pr_whir_convert_tile_leaves<3>(tile, log_n, d, log_domain, k0, cosets);
}

EXTERN __launch_bounds__(256) __global__ void ab_pr_whir_convert_tile_leaves_4_kernel(pr *tile, const u32 log_n, const proth120_twiddle_descriptor d,
                                                                                      const u32 log_domain, const u32 k0, const u32 cosets) {
  pr_whir_convert_tile_leaves<4>(tile, log_n, d, log_domain, k0, cosets);
}

EXTERN __launch_bounds__(256) __global__
    void ab_pr_whir_place_roots_kernel(const digest *retained, const u64 retained_stride, const u32 log_lde, digest *roots) {
  const u64 coset = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (coset >> log_lde)
    return;
  roots[bitreverse_low_bits(static_cast<u32>(coset), log_lde)] = retained[coset * retained_stride + retained_stride - 1];
}

} // namespace airbender::whir
