#include "context.cuh"

__device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_forward_powers;
__device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_inverse_powers;
__device__ __constant__ bf ab_inv_sizes[airbender::ntt::OMEGA_LOG_ORDER + 1];
