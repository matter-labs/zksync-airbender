#include "../gkr/support/eq_inline.cuh"
#include "../gkr/support/kernel_helpers.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::prover::gkr;

namespace airbender::prover::whir {

// Launch with gridDim.x = max(eq_group_count(challenge_count), GKR_EQ_HIGH_SLOTS):
// blocks past `groups_count` exist only to write the E::ONE() sentinel into
// degenerate high slots so inline-eq returns identity for them.
EXTERN __global__ void ab_whir_build_eq_factor_tables_batched_e4_kernel(const e4 *claim_points, const unsigned challenge_count,
                                                                        e4 *eq_high_array, e4 *eq_low_array) {
  const unsigned query_idx = blockIdx.y;
  e4 *high_slab_q = eq_high_array + static_cast<size_t>(query_idx) * GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN;
  e4 *low_buffer_q = eq_low_array + static_cast<size_t>(query_idx) * GKR_EQ_GROUP_TABLE_LEN;

  if (blockIdx.x < GKR_EQ_HIGH_SLOTS && threadIdx.x == 0) {
    high_slab_q[static_cast<size_t>(blockIdx.x) * GKR_EQ_GROUP_TABLE_LEN] = e4::ONE();
  }
  const unsigned groups_count = gkr_eq_group_count(challenge_count);
  if (blockIdx.x >= groups_count)
    return;

  const e4 *claim_point_q = claim_points + static_cast<size_t>(query_idx) * challenge_count;
  // Last group goes to the low buffer; the inner helper indexes by blockIdx.x
  // so we offset the base pointer by `-blockIdx.x * stride` to land at low[0].
  e4 *dst = (blockIdx.x + 1u == groups_count) ? low_buffer_q - static_cast<size_t>(blockIdx.x) * GKR_EQ_GROUP_TABLE_LEN : high_slab_q;
  gkr_build_eq_group_tables_from_point<e4>(claim_point_q, 0, challenge_count, dst);
}

EXTERN __global__ void ab_whir_accumulate_eq_samples_batched_e4_kernel(const e4 *eq_high_array, const e4 *eq_low_array,
                                                                       const gkr_eq_sizes sizes, const e4 *challenges, e4 *eq_poly,
                                                                       const unsigned num_queries, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  e4 acc = e4::ZERO();
  for (unsigned q = 0; q < num_queries; ++q) {
    const e4 *high_q = eq_high_array + static_cast<size_t>(q) * GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN;
    const e4 *low_q = eq_low_array + static_cast<size_t>(q) * GKR_EQ_GROUP_TABLE_LEN;
    const e4 eq = gkr_compute_eq_inline_global<e4>(high_q, high_q + GKR_EQ_GROUP_TABLE_LEN, low_q, sizes, gid);
    acc = e4::add(acc, e4::mul(eq, challenges[q]));
  }
  eq_poly[gid] = e4::add(eq_poly[gid], acc);
}

} // namespace airbender::prover::whir
