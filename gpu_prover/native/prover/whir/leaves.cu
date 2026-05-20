#include "../../common.cuh"
#include "../../ntt/context.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"
#include "../../primitives/vectorized.cuh"

using namespace ::airbender::ntt;
using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;

namespace airbender::prover::whir {

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

EXTERN __global__ void ab_pack_rows_for_whir_leaves_bf_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> src,
                                                              vectorized_e4_matrix_setter<st_modifier::cs> dst,
                                                              const unsigned log_trace_len,
                                                              const unsigned log_lde_factor,
                                                              const unsigned log_blocks_per_coset,
                                                              const unsigned log_values_per_leaf,
                                                              const unsigned dst_rows_per_coset) {
  const unsigned coset = blockIdx.x >> log_blocks_per_coset;
  const unsigned block_in_coset_mask = (1 << log_blocks_per_coset) - 1;
  const unsigned block_in_coset = blockIdx.x & block_in_coset_mask;

  src.add_row(coset << log_trace_len);
  dst.add_row(coset << (log_trace_len - log_values_per_leaf));

  const unsigned dst_row = block_in_coset * blockDim.x + threadIdx.x;
  if (dst_row >= dst_rows_per_coset)
    return;

  dst.add_row(dst_row);

  // extern __shared__ e4 smem[];
  // e4 *smem_warp = smem + 64 * threadIdx.y;

  const unsigned dst_slot_in_leaf = 2 * threadIdx.y;
  const unsigned src_row_a = dst_row + bitreverse_low_bits(dst_slot_in_leaf, log_values_per_leaf) * dst_rows_per_coset;
  const unsigned src_row_b = src_row_a + (dst_rows_per_coset << (log_values_per_leaf - 1));

  const e4 a = src.get_at_row(src_row_a);
  const e4 b = src.get_at_row(src_row_b);

  const unsigned coset_offset = bitreverse_low_bits(coset, log_lde_factor) << (OMEGA_LOG_ORDER - log_trace_len - log_lde_factor);
  const bf x_inv = get_inverse_twiddle_power((src_row_a << (OMEGA_LOG_ORDER - log_trace_len)) + coset_offset);

  const bf two_inv_power = ab_inv_sizes[log_values_per_leaf];

  const e4 c = e4::mul(two_inv_power, e4::add(a, b));
  const e4 d = e4::mul(bf::mul(x_inv, two_inv_power), e4::sub(a, b));

  dst.set_at_col(dst_slot_in_leaf, c);
  dst.set_at_col(dst_slot_in_leaf + 1, d);
}

} // namespace airbender::prover::whir
