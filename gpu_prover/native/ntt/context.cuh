#pragma once

#include "../common.cuh"
#include "../primitives/field.cuh"
#include "../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ntt {

static constexpr unsigned OMEGA_LOG_ORDER = 27;

struct powers_layer_data {
  const bf *values;
  unsigned mask;
  unsigned log_count;
};

struct powers_data_2_layer {
  powers_layer_data fine;
  powers_layer_data coarse;
};

} // namespace airbender::ntt

EXTERN __device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_forward_powers;
EXTERN __device__ __constant__ airbender::ntt::powers_data_2_layer ab_ntt_inverse_powers;
EXTERN __device__ __constant__ bf ab_inv_sizes[airbender::ntt::OMEGA_LOG_ORDER + 1];

namespace airbender::ntt {

DEVICE_FORCEINLINE bf get_power_from_layers(const powers_data_2_layer &data, const unsigned idx) {
  const unsigned fine_idx = (idx >> data.coarse.log_count) & data.fine.mask;
  const unsigned coarse_idx = idx & data.coarse.mask;
  bf value = load_ca(data.coarse.values + coarse_idx);
  if (fine_idx != 0) {
    value = bf::mul(value, load_ca(data.fine.values + fine_idx));
  }
  return value;
}

DEVICE_FORCEINLINE bf get_forward_twiddle_power(const unsigned idx) { return get_power_from_layers(::ab_ntt_forward_powers, idx); }

DEVICE_FORCEINLINE bf get_inverse_twiddle_power(const unsigned idx) { return get_power_from_layers(::ab_ntt_inverse_powers, idx); }

DEVICE_FORCEINLINE unsigned bitrev(const unsigned idx, const unsigned log_n) { return __brev(idx) >> (32 - log_n); }

} // namespace airbender::ntt
