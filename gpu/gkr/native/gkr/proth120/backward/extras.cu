#include "../../support/eq_inline.cuh"
#include "accumulator_pr.cuh"

namespace airbender::gkr::proth120::backward {

constexpr unsigned PR_EXTRAS_MAX_COLUMNS = 64;
constexpr unsigned PR_EXTRAS_THREADS = 256;

struct alignas(8) pr_extras_columns {
  const pr *values[PR_EXTRAS_MAX_COLUMNS];
};

static_assert(sizeof(void *) == 8 && sizeof(pr) == 16 && alignof(pr) == 16);
static_assert(sizeof(pr_extras_columns) == 512 && alignof(pr_extras_columns) == 8);
static_assert(sizeof(gkr_eq_sizes) == 12 && alignof(gkr_eq_sizes) == 4);
static_assert(sizeof(pr_extras_columns) + 3 * sizeof(void *) + sizeof(gkr_eq_sizes) + 2 * sizeof(unsigned) + 4 + sizeof(void *) == 568);

EXTERN __global__ __launch_bounds__(PR_EXTRAS_THREADS) void ab_pr_gkr_layer0_extras_kernel(const __grid_constant__ pr_extras_columns columns,
                                                                                           const pr *eq_high_0, const pr *eq_high_1, const pr *eq_low,
                                                                                           const gkr_eq_sizes sizes, const unsigned rows,
                                                                                           const unsigned column_count, pr *out) {
  const unsigned column = blockIdx.y;
  if (column >= column_count || column >= PR_EXTRAS_MAX_COLUMNS || blockDim.x != PR_EXTRAS_THREADS)
    return;
  const pr *values = columns.values[column];
  pr acc = pr_zero();
  for (unsigned row = blockIdx.x * PR_EXTRAS_THREADS + threadIdx.x; row < rows; row += gridDim.x * PR_EXTRAS_THREADS) {
    const pr value = load<pr, ld_modifier::cs>(values, row);
    acc = pr::add(acc, eq_low == nullptr ? value : pr::mul(value, gkr_compute_eq_inline_global<pr>(eq_high_0, eq_high_1, eq_low, sizes, row)));
  }
  __shared__ pr partial[PR_EXTRAS_THREADS];
  partial[threadIdx.x] = acc;
  __syncthreads();
#pragma unroll
  for (unsigned step = PR_EXTRAS_THREADS / 2; step > 0; step >>= 1) {
    if (threadIdx.x < step)
      partial[threadIdx.x] = pr::add(partial[threadIdx.x], partial[threadIdx.x + step]);
    __syncthreads();
  }
  if (threadIdx.x == 0)
    out[static_cast<size_t>(column) * gridDim.x + blockIdx.x] = partial[0];
}

} // namespace airbender::gkr::proth120::backward
