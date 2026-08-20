#include <common.cuh>
#include <primitives/field.cuh>
#include <primitives/memory.cuh>
#include <primitives/vectorized.cuh>

#include "context.cuh"
#include "whir_leaf_transform.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;

namespace airbender::ntt {

struct constant_inverse_power_source {
  struct {
    unsigned omega_log_order;
  } params;

  DEVICE_FORCEINLINE bf get(const unsigned idx) const { return get_inverse_twiddle_power(idx); }
};

struct matrix_leaf_destination {
  static constexpr bool ALIASES_VALUES_SMEM = false;

  vectorized_e4_matrix_setter<st_modifier::cs> dst;
  unsigned leaves_per_coset;

  DEVICE_FORCEINLINE void set_at_slot(const unsigned slot, const e4 value) { dst.set_at_row(leaves_per_coset * slot, value); }
};

// Implements "Improving running time via alternate domain evaluation" from page 15 of
// https://eprint.iacr.org/2024/1586.pdf.
// Transforms values for each leaf in-place and preserves natural coset order.
// This maximizes uniformity with the non-transformed path. In particular:
//  - Transformed output can be passed directly to ab_blake2s_leaves_from_ntt_multi_coset_kernel.
//  - Transformed leaves can still be gathered by schedule_query_merkle_paths_into_from_ntt.
// In-place safe (src and dst may alias).
EXTERN __launch_bounds__(512, 2) __global__
    void ab_transform_whir_leaves_from_ntt_multi_coset_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> src,
                                                              vectorized_e4_matrix_setter<st_modifier::cs> dst, const unsigned log_trace_len,
                                                              const unsigned log_lde_factor, const unsigned log_values_per_leaf,
                                                              const unsigned coset_index_base) {
  const unsigned gid_x = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned log_leaves_per_coset = log_trace_len - log_values_per_leaf;
  const unsigned coset = coset_index_base + (gid_x >> log_leaves_per_coset);
  const unsigned lane_in_coset_mask = (1 << log_leaves_per_coset) - 1;
  const unsigned base_lane_in_coset = gid_x & lane_in_coset_mask;

  src.add_col(coset);
  dst.add_col(coset);

  src.add_row(base_lane_in_coset);
  dst.add_row(base_lane_in_coset);

  extern __shared__ __align__(16) uint8_t smem[];

  const unsigned leaves_per_coset = 1 << log_leaves_per_coset;
  e4 *values_smem = reinterpret_cast<e4 *>(smem);
  bf *x_invs_smem = reinterpret_cast<bf *>(smem + 2 * blockDim.x * blockDim.y * sizeof(e4));
  matrix_leaf_destination destination{dst, leaves_per_coset};
  constant_inverse_power_source inverse_power_source{{OMEGA_LOG_ORDER}};
  transform_whir_leaf_from_ntt(src, destination, log_trace_len, log_lde_factor, log_values_per_leaf, coset, base_lane_in_coset, values_smem, x_invs_smem,
                               ab_inv_sizes[log_values_per_leaf], inverse_power_source);
}

} // namespace airbender::ntt
