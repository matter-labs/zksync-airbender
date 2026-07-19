#pragma once

#include <common.cuh>
#include <cstddef>
#include <primitives/field.cuh>
#include <primitives/memory.cuh>

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ntt {

static constexpr unsigned OMEGA_LOG_ORDER = 27;
// Mirrors CMEM_LOG_ORDER in src/ntt_twiddles.rs; only used to compile-check the
// CMEM_FINE_LOG_COUNT derivation below.
static constexpr int CMEM_LOG_ORDER = 19;
static constexpr int CMEM_COARSE_LOG_COUNT = 10;
static constexpr int CMEM_COARSE_MASK = (1 << CMEM_COARSE_LOG_COUNT) - 1;
// "- 1" accounts for NTT twiddle arrays only covering half the range. The Rust
// side (src/ntt_twiddles.rs) DERIVES this; here it is hardcoded, so pin the
// derivation with a static_assert so either side drifting fails its own compile.
static constexpr int CMEM_FINE_LOG_COUNT = 8;
static_assert(CMEM_FINE_LOG_COUNT == CMEM_LOG_ORDER - CMEM_COARSE_LOG_COUNT - 1);
static constexpr int CMEM_FINE_MASK = (1 << CMEM_FINE_LOG_COUNT) - 1;
static constexpr int MASK_10 = (1 << 10) - 1;
static constexpr int MASK_11 = (1 << 11) - 1;
static constexpr int MASK_12 = (1 << 12) - 1;
static constexpr int MASK_13 = (1 << 13) - 1;

struct powers_layer_data {
  const bf *values;
  unsigned mask;
  unsigned log_count;
};

struct powers_data_2_layer {
  powers_layer_data fine;
  powers_layer_data coarse;
};

// Cross-language layout drift guard. These MUST match the twin `const _: ()`
// assert block for PowersLayerData / PowersData2Layer in src/ntt_twiddles.rs:
// both sides pin the SAME explicit numbers so that either side drifting fails
// its own compile (the structs are memcpy'd verbatim into the `__constant__`
// symbols above, so any layout mismatch would silently corrupt every twiddle
// lookup). Update the twin block in ntt_twiddles.rs whenever a field changes.
static_assert(sizeof(powers_layer_data) == 16);
static_assert(alignof(powers_layer_data) == 8);
static_assert(offsetof(powers_layer_data, values) == 0);
static_assert(offsetof(powers_layer_data, mask) == 8);
static_assert(offsetof(powers_layer_data, log_count) == 12);
static_assert(sizeof(powers_data_2_layer) == 32);
static_assert(alignof(powers_data_2_layer) == 8);
static_assert(offsetof(powers_data_2_layer, fine) == 0);
static_assert(offsetof(powers_data_2_layer, coarse) == 16);

} // namespace airbender::ntt

EXTERN __device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_forward_powers;
EXTERN __device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_inverse_powers;
EXTERN __device__ __constant__ bf ab_inv_sizes[airbender::ntt::OMEGA_LOG_ORDER + 1];

// Use cmem twiddles for stages where warps access them uniformly
EXTERN __device__ __constant__ base_field ab_fwd_cmem_twiddles_coarse[1 << ::airbender::ntt::CMEM_COARSE_LOG_COUNT];
EXTERN __device__ __constant__ base_field ab_inv_cmem_twiddles_coarse[1 << ::airbender::ntt::CMEM_COARSE_LOG_COUNT];
EXTERN __device__ __constant__ base_field ab_fwd_cmem_twiddles_fine[1 << ::airbender::ntt::CMEM_FINE_LOG_COUNT];
EXTERN __device__ __constant__ base_field ab_inv_cmem_twiddles_fine[1 << ::airbender::ntt::CMEM_FINE_LOG_COUNT];
EXTERN __device__ __constant__ base_field ab_fwd_cmem_twiddles_finest_10[1 << 10];
EXTERN __device__ __constant__ base_field ab_inv_cmem_twiddles_finest_10[1 << 10];
EXTERN __device__ __constant__ base_field ab_fwd_cmem_twiddles_finest_11[1 << 11];
EXTERN __device__ __constant__ base_field ab_inv_cmem_twiddles_finest_11[1 << 11];

// Use swizzled twiddles for stages where consecutive threads access them with a strided pattern.
EXTERN __device__ __constant__ const base_field *ab_fwd_gmem_twiddles_coarse;
EXTERN __device__ __constant__ const base_field *ab_inv_gmem_twiddles_coarse;

// Use fully precomputed twiddles for LDEs with log_n <= 18.
EXTERN __device__ __constant__ const base_field *ab_fully_precomputed_bitrev_twiddles;

namespace airbender::ntt {

DEVICE_FORCEINLINE bf get_power_from_layers(const powers_data_2_layer &data, const unsigned idx) {
  const unsigned coarse_idx = (idx >> data.fine.log_count) & data.coarse.mask;
  const unsigned fine_idx = idx & data.fine.mask;
  bf value = load_ca(data.coarse.values + coarse_idx);
  if (fine_idx != 0) {
    value = bf::mul(value, load_ca(data.fine.values + fine_idx));
  }
  return value;
}

DEVICE_FORCEINLINE bf get_forward_twiddle_power(const unsigned idx) { return get_power_from_layers(::ab_ntt_forward_powers, idx); }

DEVICE_FORCEINLINE bf get_inverse_twiddle_power(const unsigned idx) { return get_power_from_layers(::ab_ntt_inverse_powers, idx); }

// In-crate name kept to avoid call-site churn; delegates to gpu_core's guarded helper (common.cuh).
DEVICE_FORCEINLINE unsigned bitrev(const unsigned idx, const unsigned log_n) { return ::bitreverse_low_bits(idx, log_n); }

} // namespace airbender::ntt
