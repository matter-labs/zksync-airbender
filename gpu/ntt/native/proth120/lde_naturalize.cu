#include "context.cuh"

namespace airbender::ntt {

DEVICE_FORCEINLINE uint2 triangular_index_flat_to_two_dim(const unsigned index, const unsigned m) {
  const unsigned ii = m * (m + 1) / 2 - 1 - index;
  const unsigned k = floor((sqrtf(static_cast<float>(8 * ii + 1)) - 1) / 2);
  const unsigned jj = ii - k * (k + 1) / 2;
  const unsigned x = m - 1 - jj;
  const unsigned y = m - 1 - k;
  return {x, y};
}

EXTERN __launch_bounds__(128) __global__
    void ab_pr_naturalize_kernel(const pr_matrix_getter<ld_modifier::cs> src, const pr_matrix_setter<st_modifier::cs> dst, const unsigned log_count) {
  using T = pr;
  static constexpr unsigned LOG_CHUNK_SIZE = 0;
  static constexpr unsigned CHUNK_SIZE = 1u << LOG_CHUNK_SIZE;
  static constexpr unsigned LOG_TILE_DIM = 5 - LOG_CHUNK_SIZE;
  static constexpr unsigned TILE_DIM = 1u << LOG_TILE_DIM;
  static constexpr unsigned BLOCK_ROWS = 2;
  __shared__ T tile[2][TILE_DIM][(TILE_DIM + 1) << LOG_CHUNK_SIZE];
  const unsigned tid_x = threadIdx.x;
  const unsigned tid_y = threadIdx.y;
  const unsigned col = blockIdx.z;
  const unsigned half_log_count = log_count >> 1;
  const unsigned stride = gridDim.y << (half_log_count + LOG_CHUNK_SIZE);
  const unsigned x_offset = (blockIdx.y << (half_log_count + LOG_CHUNK_SIZE)) + tid_x;
  const unsigned m = 1u << (half_log_count - LOG_TILE_DIM);
  const auto [x, y] = triangular_index_flat_to_two_dim(blockIdx.x, m);
  const bool is_diagonal = x == y;
  const unsigned is_reverse = threadIdx.z;
  if (is_diagonal && is_reverse)
    return;
  const unsigned tile_x = is_reverse ? y : x;
  const unsigned tile_y = is_reverse ? x : y;
  const unsigned tile_x_offset = tile_x * TILE_DIM;
  const unsigned tile_y_offset = tile_y * TILE_DIM;
  const unsigned x_src = (tile_x_offset << LOG_CHUNK_SIZE) + x_offset;
  const unsigned y_src = tile_y_offset + tid_y;
  const unsigned x_dst = (tile_y_offset << LOG_CHUNK_SIZE) + x_offset;
  const unsigned y_dst = tile_x_offset + tid_y;
#pragma unroll
  for (int i = 0; i < TILE_DIM; i += BLOCK_ROWS) {
    const unsigned idx = tid_y + i;
    const unsigned ry = bitreverse_low_bits(y_src + i, half_log_count);
    const T value = src.get(ry * stride + x_src, col);
    tile[is_reverse][idx][tid_x] = value;
  }
  __syncthreads();
#pragma unroll
  for (int i = 0; i < TILE_DIM; i += BLOCK_ROWS) {
    const unsigned idx = tid_y + i;
    const unsigned ry = bitreverse_low_bits(y_dst + i, half_log_count);
    T value = tile[is_reverse][tid_x >> LOG_CHUNK_SIZE][idx << LOG_CHUNK_SIZE | (tid_x & (CHUNK_SIZE - 1))];
    dst.set(ry * stride + x_dst, col, value);
  }
}

EXTERN __launch_bounds__(256) __global__ void ab_pr_naturalize_naive_kernel(pr_matrix_getter_setter<ld_modifier::cs, st_modifier::cs> values, const u32 log_n) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= (1u << log_n))
    return;
  const u32 j = bitreverse_low_bits(i, log_n);
  if (i >= j)
    return;
  values.add_col(blockIdx.y);
  const pr a = values.get_at_row(i);
  const pr b = values.get_at_row(j);
  values.set_at_row(i, b);
  values.set_at_row(j, a);
}

} // namespace airbender::ntt
