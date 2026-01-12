#include "radix_8_utils.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(128, 8) __global__
    void ab_bit_reverse_by_radix_8(vectorized_e2_matrix_getter<ld_modifier::cg> src, vectorized_e2_matrix_setter<st_modifier::cg> dst,
                                   const unsigned bit_chunks, const unsigned log_n) {
  const unsigned n = 1 << log_n;
  const unsigned l_index = blockIdx.x * blockDim.x + threadIdx.x;
  if (l_index >= n)
    return;
  const unsigned r_index = bitrev_by_radix<3>(l_index, bit_chunks);
  if (l_index > r_index)
    return;
  const e2 l_value = src.get_at_row(l_index);
  const e2 r_value = src.get_at_row(r_index);
  dst.set_at_row(l_index, r_value);
  dst.set_at_row(r_index, l_value);
}

} // namespace airbender::ntt
