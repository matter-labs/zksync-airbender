#include "context.cuh"
#include "ops_complex.cuh"
#include "vectorized.cuh"

using namespace ::airbender::field;
using namespace ::airbender::memory;
using namespace ::airbender::ops_complex;
using namespace ::airbender::vectorized;

namespace airbender::barycentric {

using bf = base_field;
using e2 = ext2_field;
using e4 = ext4_field;

// NB: Argument Types
// Barycentric eval is used to evaluate trace, argument, and split-quotient polys
// at some challenge point "z". It works by multiplies each poly's evals on a particular
// domain by a set of precomputed lagrange coeffs specific to z and that domain.
// The challenge point is always e4.
// The domain we typically use is the first circle coset LDE domain, whose values are e2.
// Trace poly evals are read as bf "compressed" values on this domain.
// Split-quotient evals are e4.

// Helper functions to compute common_factor for precompute_lagrange_coeffs
EXTERN __global__ void ab_barycentric_precompute_common_factor_kernel(const e4 *z_ref, e4 *common_factor_ref, const e2 coset, const e2 decompression_factor,
                                                                      const unsigned count) {
  // common_factor = coset * (z^N - coset^N) / (N * coset^N)
  // Note that common_factor depends on z through z^N.
  // The "shift trick" used in the partial reduce kernel to compute evals at z, omega * z, omega^2 * z, etc...
  // using the coeffs at z only works because omega^N = 1, which means common_factor at omega * z, omega^2 * z, etc...
  // is the same as common_factor at z.
  // some math could be done on the CPU, but this is a 1-thread kernel so hopefully negligible
  const e4 z = *z_ref;
  const e2 cosetN = e2::pow(coset, count);
  const e4 zN = e4::pow(z, count);
  const e4 num = e4::mul(e4::sub(zN, cosetN), coset);
  const e2 denom = e2::mul(bf{count}, cosetN);
  const e2 denom_inv = e2::inv(denom);
  // Ensures decompression of batch_ys if they were compressed according to
  // https://eprint.iacr.org/2023/824.pdf
  // Assumes c0 = 0 (in the notation of equation 7).
  // If batch_ys are uncompressed, caller should pass decompression_factor = E2::ONE
  const e2 denom_inv_with_decompression = e2::mul(denom_inv, decompression_factor);
  const e4 common_factor = e4::mul(num, denom_inv_with_decompression);
  *common_factor_ref = common_factor;
}

// TODO: Deep quotiening needs 1 / (w^i - z). We could stash an intermediate here that deep could use.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_barycentric_precompute_lagrange_coeffs_kernel(const e4 *z_ref, const e4 *common_factor_ref, const e2 w_inv_step, const e2 coset,
                                                          vector_setter<e4, st_modifier::cs> lagrange_coeffs, const unsigned log_count) {
  constexpr unsigned INV_BATCH = InvBatch<e4>::INV_BATCH;

  // per_elem_factor = w^i / (z - coset * w^i)
  //                 = 1 / ((z / w^i) - coset)
  // lagrange_coeff = common_factor * per_elem_factor
  // In per_elem_factor, we can get 1 / w_i "for free" by passing inverse=true to get_power_of_w_device.

  const auto common_factor = *common_factor_ref;

  const unsigned count = 1u << log_count;
  const auto gid = unsigned(blockIdx.x * blockDim.x + threadIdx.x);
  if (gid >= count)
    return;

  const auto grid_size = unsigned(blockDim.x * gridDim.x);

  e4 per_elem_factor_invs[INV_BATCH];

  const e4 z = *z_ref;
  unsigned runtime_batch_size = 0;
  const unsigned shift = CIRCLE_GROUP_LOG_ORDER - log_count;
  auto w_inv = get_power_of_w(gid << shift, true);
#pragma unroll
  for (unsigned i{0}, g{gid}; i < INV_BATCH; i++, g += grid_size)
    if (g < count) {
      per_elem_factor_invs[i] = e4::sub(e4::mul(z, w_inv), coset);
      if (g + grid_size < count)
        w_inv = e2::mul(w_inv, w_inv_step);
      runtime_batch_size++;
    }

  e4 per_elem_factors[INV_BATCH];

  if (runtime_batch_size < INV_BATCH) {
    batch_inv_registers<e4, INV_BATCH, false>(per_elem_factor_invs, per_elem_factors, runtime_batch_size);
  } else {
    batch_inv_registers<e4, INV_BATCH, true>(per_elem_factor_invs, per_elem_factors, runtime_batch_size);
  }

#pragma unroll
  for (unsigned i{0}, g{gid}; i < INV_BATCH; i++, g += grid_size)
    if (g < count)
      lagrange_coeffs.set(g, e4::mul(per_elem_factors[i], common_factor));
}

constexpr unsigned MAX_COLS = 1344;
constexpr unsigned DOES_NOT_NEED_Z_OMEGA = UINT_MAX;

struct ColIdxsToEvalAtZOmegaIdxsMap {
  const unsigned map[MAX_COLS];
};

template <bool ANY_AT_Z_OMEGA, typename GETTER_T, bool IS_COMPOSITION_COL = false>
DEVICE_FORCEINLINE void accumulate(GETTER_T &cols_in, const e4 *coeff_chunk, const matrix_setter<e4, st_modifier::cs> &partial_sums,
                                   const ColIdxsToEvalAtZOmegaIdxsMap &map, const unsigned num_cols, const unsigned row_chunk_size,
                                   const unsigned block_row_offset, const unsigned n, unsigned &col_offset, const e2 decompression_factor_inv) {
  cols_in.add_row(block_row_offset + threadIdx.x);
  // The logic here effectively flattens the sequence of setup cols, witness cols, memory cols, stage 2 cols...etc
  // for better load balancing across warps
  const unsigned col_offset_mod_num_warps = col_offset & 16;
  unsigned col_start_in_cols_in{};
  if (threadIdx.y >= col_offset_mod_num_warps)
    col_start_in_cols_in = threadIdx.y - col_offset_mod_num_warps;
  else
    col_start_in_cols_in = (threadIdx.y + 16 - col_offset_mod_num_warps);
  cols_in.add_col(col_start_in_cols_in);
#pragma unroll 1
  for (unsigned col = col_start_in_cols_in; col < num_cols; col += blockDim.y, cols_in.add_col(blockDim.y)) {
    GETTER_T cols{cols_in}; // default copy constructor :fingers crossed:
    e4 sum_at_z{e4::zero()};
    e4 sum_at_z_omega{e4::zero()};
    const unsigned maybe_eval_at_z_omega_idx = map.map[col_offset + col];
#pragma unroll 1
    for (unsigned thread_row_offset = threadIdx.x; (thread_row_offset < row_chunk_size) && (block_row_offset + thread_row_offset < n);
         thread_row_offset += blockDim.x, cols.add_row(blockDim.x)) {
      const auto coset_eval = cols.get();
      const auto coeff = coeff_chunk[thread_row_offset + 1];
      sum_at_z = e4::add(sum_at_z, e4::mul(coeff, coset_eval));
      if (ANY_AT_Z_OMEGA)
        if (maybe_eval_at_z_omega_idx != DOES_NOT_NEED_Z_OMEGA) {
          const auto coeff = coeff_chunk[thread_row_offset];
          sum_at_z_omega = e4::add(sum_at_z_omega, e4::mul(coeff, coset_eval));
        }
    }

    const unsigned row_out = std::min(row_chunk_size, blockDim.x) * blockIdx.x + threadIdx.x;
    // If this block was assigned to the bottom few rows, or if row_chunk_size is small,
    // it's possible some threads have no data to write.
    const unsigned row_tail = std::min(row_chunk_size, n - block_row_offset);
    if (threadIdx.x < row_tail) {
      if (IS_COMPOSITION_COL)
        sum_at_z = e4::mul(sum_at_z, decompression_factor_inv); // composition col evals are NOT compressed
      partial_sums.set(row_out, col + col_offset, sum_at_z);
      if (ANY_AT_Z_OMEGA)
        if (maybe_eval_at_z_omega_idx != DOES_NOT_NEED_Z_OMEGA)
          partial_sums.set(row_out, maybe_eval_at_z_omega_idx, sum_at_z_omega);
    }
  }
  col_offset += num_cols;
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_barycentric_partial_reduce_kernel(matrix_getter<bf, ld_modifier::cs> setup_cols, matrix_getter<bf, ld_modifier::cs> witness_cols,
                                              matrix_getter<bf, ld_modifier::cs> memory_cols, matrix_getter<bf, ld_modifier::cs> stage_2_bf_cols,
                                              vectorized_e4_matrix_getter<ld_modifier::cs> stage_2_e4_cols,
                                              vectorized_e4_matrix_getter<ld_modifier::cs> composition_col, vector_getter<e4, ld_modifier::ca> lagrange_coeffs,
                                              matrix_setter<e4, st_modifier::cs> partial_sums, __grid_constant__ const ColIdxsToEvalAtZOmegaIdxsMap map,
                                              const e2 decompression_factor_inv, const unsigned num_setup_cols, const unsigned num_witness_cols,
                                              const unsigned num_memory_cols, const unsigned num_stage_2_bf_cols, const unsigned num_stage_2_e4_cols,
                                              const unsigned row_chunk_size, const unsigned log_n) {
  // TODO: make sure the slightly-ragged smem allocation does not hurt occupancy
  // We could eliminate raggedness by fetching elems in the "shift tail" from gmem on demand, and hope for L1 hits.
  // We could even eliminate smem altogether, just read lagrange coeffs on demand, and hope for L1 hits.
  // Let's try making them all first-class citizens in smem first and see how it performs.
  extern __shared__ e4 coeff_chunk[];

  const unsigned n = 1u << log_n;

  // Cooperatively load this block's coeff chunk
  // I could imagine an alternative implementation where each thread loads its own coeff value,
  // then we cooperatively load an eval chunk
  unsigned block_row_offset = row_chunk_size * blockIdx.x;
  unsigned flat_thread_row_offset = blockDim.x * threadIdx.y + threadIdx.x;
  if (block_row_offset + flat_thread_row_offset == 0) {
    coeff_chunk[flat_thread_row_offset] = lagrange_coeffs.get(n - 1);
  } else {
    if ((flat_thread_row_offset < row_chunk_size + 1) && (block_row_offset + flat_thread_row_offset - 1 < n))
      coeff_chunk[flat_thread_row_offset] = lagrange_coeffs.get(block_row_offset + flat_thread_row_offset - 1);
  }
  flat_thread_row_offset += blockDim.x * blockDim.y;
  for (; (flat_thread_row_offset < row_chunk_size + 1) && (block_row_offset + flat_thread_row_offset - 1 < n);
       flat_thread_row_offset += blockDim.x * blockDim.y)
    coeff_chunk[flat_thread_row_offset] = lagrange_coeffs.get(block_row_offset + flat_thread_row_offset - 1);

  __syncthreads();

  // Now this block can go wild and accumulate the sums for z and (if necessary) z * omega for all columns in the row-chunk.
  // Each warp is assigned to one col of coset evals at a time, and computes all sums for the row-chunk of that col before
  // moving to its next assigned col. This approach ensures each eval is read only once.
  unsigned col_offset = 0;
  accumulate<false>(setup_cols, coeff_chunk, partial_sums, map, num_setup_cols, row_chunk_size, block_row_offset, n, col_offset, decompression_factor_inv);
  accumulate<true>(witness_cols, coeff_chunk, partial_sums, map, num_witness_cols, row_chunk_size, block_row_offset, n, col_offset, decompression_factor_inv);
  accumulate<true>(memory_cols, coeff_chunk, partial_sums, map, num_memory_cols, row_chunk_size, block_row_offset, n, col_offset, decompression_factor_inv);
  accumulate<false>(stage_2_bf_cols, coeff_chunk, partial_sums, map, num_stage_2_bf_cols, row_chunk_size, block_row_offset, n, col_offset,
                    decompression_factor_inv);
  accumulate<true>(stage_2_e4_cols, coeff_chunk, partial_sums, map, num_stage_2_e4_cols, row_chunk_size, block_row_offset, n, col_offset,
                   decompression_factor_inv);
  accumulate<false, decltype(composition_col), true>(composition_col, coeff_chunk, partial_sums, map, 1, row_chunk_size, block_row_offset, n, col_offset,
                                                     decompression_factor_inv);
}

} // namespace airbender::barycentric