#include "context.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(256) __global__
    void ab_pr_lde_scale_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const pr *offset, const u32 rows) {
  const u32 t = blockIdx.x * blockDim.x + threadIdx.x;
  if (t >= rows)
    return;
  const u32 stride = gridDim.x * blockDim.x;
  const pr value = load_ca(offset);
  pr power = pr::pow(value, t);
  const pr step = pr::pow(value, stride);
  in.add_col(blockIdx.y);
  out.add_col(blockIdx.y);
  for (u32 row = t; row < rows; row += stride) {
    out.set_at_row(row, pr::mul(in.get_at_row(row), power));
    power = pr::mul(power, step);
  }
}

EXTERN __launch_bounds__(256) __global__
    void ab_pr_lde_scale_table_kernel(const pr *in, pr *out, const proth120_twiddle_descriptor d, const u32 log_n, const u32 k0) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  const u32 k = k0 + blockIdx.y;
  const u32 exponent = static_cast<u32>(static_cast<u64>(k) * i) & 0x7fffffffu;
  const pr value = pr::mul(load_cg(in + i), pr_root_power(d, exponent));
  store_cg(out + (static_cast<size_t>(blockIdx.y) << log_n) + i, value);
}

} // namespace airbender::ntt
