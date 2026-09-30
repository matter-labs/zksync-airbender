#pragma once

#include <common.cuh>
#include <cstddef>
#include <primitives/field.cuh>
#include <primitives/memory.cuh>

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ntt {

struct whir_leaf_transform_params {
  const bf *inverse_fine_values;
  unsigned inverse_fine_mask;
  unsigned inverse_fine_log_count;
  const bf *inverse_coarse_values;
  unsigned inverse_coarse_mask;
  unsigned omega_log_order;
};

// Twin of `WhirLeafTransformParams` in `src/ntt_twiddles.rs`.
static_assert(sizeof(whir_leaf_transform_params) == 32);
static_assert(alignof(whir_leaf_transform_params) == 8);
static_assert(offsetof(whir_leaf_transform_params, inverse_fine_values) == 0);
static_assert(offsetof(whir_leaf_transform_params, inverse_fine_mask) == 8);
static_assert(offsetof(whir_leaf_transform_params, inverse_fine_log_count) == 12);
static_assert(offsetof(whir_leaf_transform_params, inverse_coarse_values) == 16);
static_assert(offsetof(whir_leaf_transform_params, inverse_coarse_mask) == 24);
static_assert(offsetof(whir_leaf_transform_params, omega_log_order) == 28);

struct params_inverse_power_source {
  whir_leaf_transform_params params;

  DEVICE_FORCEINLINE bf get(const unsigned idx) const {
    const unsigned coarse_idx = (idx >> params.inverse_fine_log_count) & params.inverse_coarse_mask;
    const unsigned fine_idx = idx & params.inverse_fine_mask;
    bf value = load_ca(params.inverse_coarse_values + coarse_idx);
    if (fine_idx != 0) {
      value = bf::mul(value, load_ca(params.inverse_fine_values + fine_idx));
    }
    return value;
  }
};

} // namespace airbender::ntt
