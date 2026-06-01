#include "common.cuh"
#include "primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::ops {

// Materializes [base^(2^0), base^(2^1), ..., base^(2^(count-1))] for E4.
// E.g. result[0] = base, result[1] = base^2, result[2] = base^4, etc.
// `count` is small (== log_n, typically <= 25), so we use a single-thread
// sequential loop — launch with grid=1, block=1.
EXTERN __global__ void ab_squaring_sequence_e4_kernel(const e4 *base, e4 *result, const unsigned count) {
  if (threadIdx.x != 0 || blockIdx.x != 0)
    return;
  if (count == 0)
    return;
  e4 value = *base;
  for (unsigned i = 0; i < count; ++i) {
    result[i] = value;
    value = e4::sqr(value);
  }
}

// For each query i in [0, num_queries):
//   point = e4::from_scalar(domain_generator ** query_indexes[i])
//   result[i*count_per_query + 0] = point
//   result[i*count_per_query + 1] = point^2
//   result[i*count_per_query + 2] = point^4
//   ...
//   result[i*count_per_query + count_per_query - 1] = point ** 2^(count_per_query - 1)
// One thread (block) per query. `count_per_query` is small (<= log_n, ~25).
EXTERN __global__ void ab_query_squaring_sequences_bf_to_e4_kernel(const bf domain_generator, const unsigned *query_indexes, e4 *result,
                                                                   const unsigned count_per_query, const unsigned num_queries) {
  const unsigned q = blockIdx.x * blockDim.x + threadIdx.x;
  if (q >= num_queries)
    return;
  if (count_per_query == 0)
    return;
  const unsigned qi = query_indexes[q];
  const bf base_bf = bf::pow(domain_generator, qi);
  e4 value = e4::from_scalar(base_bf);
  e4 *dst = result + static_cast<size_t>(q) * count_per_query;
  for (unsigned i = 0; i < count_per_query; ++i) {
    dst[i] = value;
    value = e4::sqr(value);
  }
}

} // namespace airbender::ops
