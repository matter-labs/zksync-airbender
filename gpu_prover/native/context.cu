#include "context.cuh"

using namespace ::airbender::field;

__device__ __constant__ powers_data_3_layer ab_powers_data_w;
__device__ __constant__ powers_data_2_layer ab_powers_data_w_bitrev_for_ntt;
__device__ __constant__ powers_data_2_layer ab_powers_data_w_inv_bitrev_for_ntt;
__device__ __constant__ base_field ab_inv_sizes[OMEGA_LOG_ORDER + 1];
