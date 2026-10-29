#include "context.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(256) __global__
    void ab_pr_pack_columns_kernel(pr_matrix_getter<ld_modifier::cs> in, pr *out_column, const u32 log_rows, const u32 cols_in_group, const u32 group_width) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= group_width << log_rows)
    return;
  const u32 b = i >> log_rows;
  const u32 r = i & ((1u << log_rows) - 1u);
  out_column[i] = b < cols_in_group ? in.get(r, b) : pr::ZERO();
}

} // namespace airbender::ntt
