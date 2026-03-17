#include "context.cuh"

__device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_forward_powers;
__device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_inverse_powers;
__device__ __constant__ bf ab_inv_sizes[airbender::ntt::OMEGA_LOG_ORDER + 1];

// Use cmem twiddles for stages where warps access them uniformly
__device__ __constant__ base_field ab_fwd_cmem_twiddles_coarse[1 << ::airbender::ntt::CMEM_COARSE_LOG_COUNT];
__device__ __constant__ base_field ab_inv_cmem_twiddles_coarse[1 << ::airbender::ntt::CMEM_COARSE_LOG_COUNT];
__device__ __constant__ base_field ab_fwd_cmem_twiddles_fine[1 << ::airbender::ntt::CMEM_FINE_LOG_COUNT];
__device__ __constant__ base_field ab_inv_cmem_twiddles_fine[1 << ::airbender::ntt::CMEM_FINE_LOG_COUNT];
__device__ __constant__ base_field ab_fwd_cmem_twiddles_finest_10[1 << 10];
__device__ __constant__ base_field ab_inv_cmem_twiddles_finest_10[1 << 10];
__device__ __constant__ base_field ab_fwd_cmem_twiddles_finest_11[1 << 11];
__device__ __constant__ base_field ab_inv_cmem_twiddles_finest_11[1 << 11];

// Use swizzled twiddles for stages where consecutive threads access them with a strided pattern.
__device__ __constant__ const base_field *ab_fwd_gmem_twiddles_coarse;
__device__ __constant__ const base_field *ab_inv_gmem_twiddles_coarse;
