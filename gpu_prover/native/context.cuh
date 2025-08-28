#pragma once
#include "field.cuh"
#include "memory.cuh"

using namespace ::airbender::field;
using namespace ::airbender::memory;

namespace airbender::field {

// TODO:
// Decide max order we need based on trace column length and constraint degree
static constexpr unsigned OMEGA_LOG_ORDER = 25;
static constexpr unsigned CIRCLE_GROUP_LOG_ORDER = 31;

struct powers_layer_data {
  const ext2_field *values;
  unsigned mask;
  unsigned log_count;
};

struct powers_data_2_layer {
  powers_layer_data fine;
  powers_layer_data coarse;
};

struct powers_data_3_layer {
  powers_layer_data fine;
  powers_layer_data coarser;
  powers_layer_data coarsest;
};

} // namespace airbender::field

EXTERN __device__ __constant__ powers_data_3_layer ab_powers_data_w;
EXTERN __device__ __constant__ powers_data_2_layer ab_powers_data_w_bitrev_for_ntt;
EXTERN __device__ __constant__ powers_data_2_layer ab_powers_data_w_inv_bitrev_for_ntt;
EXTERN __device__ __constant__ base_field ab_inv_sizes[OMEGA_LOG_ORDER + 1];

namespace airbender::field {

DEVICE_FORCEINLINE ext2_field get_power(const powers_data_3_layer &data, const unsigned index, const bool inverse) {
  const unsigned idx = inverse ? (1u << CIRCLE_GROUP_LOG_ORDER) - index : index;

  const unsigned coarsest_idx = (idx >> (data.fine.log_count + data.coarser.log_count)) & data.coarsest.mask;
  ext2_field val = load_ca(data.coarsest.values + coarsest_idx);

  const unsigned coarser_idx = (idx >> data.fine.log_count) & data.coarser.mask;
  if (coarser_idx != 0)
    val = ext2_field::mul(val, load_ca(data.coarser.values + coarser_idx));

  const unsigned fine_idx = idx & data.fine.mask;
  if (fine_idx != 0)
    val = ext2_field::mul(val, load_ca(data.fine.values + fine_idx));

  return val;
}

DEVICE_FORCEINLINE ext2_field get_power_of_w(const unsigned index, const bool inverse) { return get_power(ab_powers_data_w, index, inverse); }

} // namespace airbender::field
