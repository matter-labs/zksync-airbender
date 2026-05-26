#include "../gkr/support/eq_inline.cuh"
#include "../gkr/support/kernel_helpers.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::prover::gkr;

namespace airbender::prover::whir {

// Launch with gridDim.x = max(eq_group_count(challenge_count), GKR_EQ_HIGH_SLOTS):
// blocks past `groups_count` exist only to write the E::ONE() sentinel into
// degenerate high slots so inline-eq returns identity for them.
EXTERN __global__ void ab_whir_build_eq_factor_tables_batched_e4_kernel(const e4 *claim_points, const unsigned challenge_count, e4 *eq_high_array,
                                                                        e4 *eq_low_array) {
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

EXTERN __global__ void ab_whir_accumulate_eq_samples_batched_e4_kernel(const e4 *eq_high_array, const e4 *eq_low_array, const gkr_eq_sizes sizes,
                                                                       const e4 *challenges, e4 *eq_poly, const unsigned num_queries, const unsigned acc_size) {
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

// WHIR 2-chunk factored-eq build kernel.
//
// For each query `q` (gridDim.y), emits a table of size `1 << bits` E4 entries:
//   out[q][idx] = product_{i in 0..bits} (bit_i(idx) ? claim_point[q][claim_offset + i]
//                                                    : 1 - claim_point[q][claim_offset + i])
// where bit_i(idx) is the i-th bit of `idx` MSB-first, matching the GKR
// builder convention (claim_point[0] -> high-order bit). If `scales` is
// non-null, every entry is additionally multiplied by `scales[q]`; this is
// how we fold `challenges[q]` into the low slab so the accumulator's inner
// loop drops to one mul per query.
//
// Build cost per query is `bits * (1 << bits)` E4 muls — trivial vs. the
// accumulator workload (build is called once per WHIR round, accumulator runs
// over the full folded-polynomial length).
EXTERN __global__ void ab_whir_build_split_eq_table_e4_kernel(const e4 *claim_points, const e4 *scales, const unsigned log_n, const unsigned bits,
                                                              const unsigned claim_offset, e4 *out_array) {
  const unsigned table_size = 1u << bits;
  const unsigned q = blockIdx.y;
  const unsigned out_idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (out_idx >= table_size)
    return;

  const e4 *claim_q = claim_points + static_cast<size_t>(q) * log_n + claim_offset;
  e4 *table_q = out_array + static_cast<size_t>(q) * table_size;

  e4 acc;
  for (unsigned i = 0; i < bits; ++i) {
    const unsigned bit_set = (out_idx >> (bits - 1u - i)) & 1u;
    const e4 p = load<e4, ld_modifier::ca>(claim_q, i);
    const e4 factor = bit_set ? p : e4::sub(e4::ONE(), p);
    acc = (i == 0) ? factor : e4::mul(acc, factor);
  }
  if (scales != nullptr) {
    const e4 scale = load<e4, ld_modifier::ca>(scales, q);
    acc = e4::mul(acc, scale);
  }
  store<e4, st_modifier::cs>(table_q, acc, out_idx);
}

// WHIR 2-chunk factored-eq accumulator.
//
// Replaces the 3-slot (high0/high1/low) GKR layout with a balanced 2-chunk
// split: `high_bits = ceil(log_n / 2)`, `low_bits = log_n - high_bits`.
// The low slab is pre-scaled by `challenges[q]` in the builder so the inner
// loop is one E4 mul + one E4 add per query. `eq_poly[gid]` is RMW'd at the
// end (matches the existing batched accumulator's contract).
EXTERN __global__ void ab_whir_accumulate_eq_split_e4_kernel(const e4 *eq_high_array, const e4 *eq_low_array, const unsigned high_bits, const unsigned low_bits,
                                                             e4 *eq_poly, const unsigned num_queries, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const unsigned high_size = 1u << high_bits;
  const unsigned low_size = 1u << low_bits;
  const unsigned hi_idx = (gid >> low_bits) & (high_size - 1u);
  const unsigned lo_idx = gid & (low_size - 1u);

  e4 acc = e4::ZERO();
  for (unsigned q = 0; q < num_queries; ++q) {
    const e4 *high_q = eq_high_array + static_cast<size_t>(q) * high_size;
    const e4 *low_q = eq_low_array + static_cast<size_t>(q) * low_size;
    const e4 hi = load<e4, ld_modifier::ca>(high_q, hi_idx);
    const e4 lo = load<e4, ld_modifier::cs>(low_q, lo_idx);
    acc = e4::add(acc, e4::mul(hi, lo));
  }
  eq_poly[gid] = e4::add(eq_poly[gid], acc);
}

} // namespace airbender::prover::whir
