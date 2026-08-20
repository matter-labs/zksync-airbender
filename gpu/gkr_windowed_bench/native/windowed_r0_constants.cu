#include "windowed_r0_abi.cuh"

using namespace ::airbender::primitives::field;

__device__ __constant__ e4 ab_gkr_windowed_r0_coeff_bank[airbender::gkr_windowed_bench::R0_COEFFICIENT_CAPACITY];
__device__ __constant__ e4 ab_gkr_windowed_r0_eq_high[airbender::gkr_windowed_bench::R0_EQ_HIGH_ELEMENTS];

static_assert(airbender::gkr_windowed_bench::R0_CONSTANT_FOOTPRINT_BYTES <= airbender::gkr_windowed_bench::R0_CONSTANT_MEMORY_CEILING_BYTES);
