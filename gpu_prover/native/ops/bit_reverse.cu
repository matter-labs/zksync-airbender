#include "../common.cuh"
#include "../primitives/field.cuh"
#include "../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ops {

struct __align__(32) dg { bf values[8]; };

template <class T>
DEVICE_FORCEINLINE void bit_reverse_naive(const matrix_getter<T, ld_modifier::cs> src, const matrix_setter<T, st_modifier::cs> dst, const unsigned log_count) {
  const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
  if (row >= 1u << log_count)
    return;
  const unsigned col = blockIdx.y;
  const unsigned l_index = row;
  const unsigned r_index = __brev(l_index) >> (32 - log_count);
  if (l_index > r_index)
    return;
  const T l_value = src.get(l_index, col);
  const T r_value = src.get(r_index, col);
  dst.set(l_index, col, r_value);
  dst.set(r_index, col, l_value);
}

#define BIT_REVERSE_NAIVE(arg_t)                                                                                                                               \
  EXTERN __global__ void ab_bit_reverse_naive_##arg_t##_kernel(const matrix_getter<arg_t, ld_modifier::cs> src,                                                \
                                                               const matrix_setter<arg_t, st_modifier::cs> dst, const unsigned log_count) {                    \
    bit_reverse_naive(src, dst, log_count);                                                                                                                    \
  }

BIT_REVERSE_NAIVE(bf);
BIT_REVERSE_NAIVE(e2);
BIT_REVERSE_NAIVE(e4);
BIT_REVERSE_NAIVE(dg);

DEVICE_FORCEINLINE uint2 triangular_index_flat_to_two_dim(const unsigned index, const unsigned m) {
  const unsigned ii = m * (m + 1) / 2 - 1 - index;
  const unsigned k = floor((sqrtf(static_cast<float>(8 * ii + 1)) - 1) / 2);
  const unsigned jj = ii - k * (k + 1) / 2;
  const unsigned x = m - 1 - jj;
  const unsigned y = m - 1 - k;
  return {x, y};
}

template <class T, unsigned LOG_CHUNK_SIZE>
DEVICE_FORCEINLINE void bit_reverse(const matrix_getter<T, ld_modifier::cs> src, const matrix_setter<T, st_modifier::cs> dst, const unsigned log_count) {
  static constexpr unsigned CHUNK_SIZE = 1u << LOG_CHUNK_SIZE;
  static constexpr unsigned LOG_TILE_DIM = 5 - LOG_CHUNK_SIZE;
  static constexpr unsigned TILE_DIM = 1u << LOG_TILE_DIM;
  static constexpr unsigned BLOCK_ROWS = 2;
  __shared__ T tile[2][TILE_DIM][(TILE_DIM + 1) << LOG_CHUNK_SIZE];
  const unsigned tid_x = threadIdx.x;
  const unsigned tid_y = threadIdx.y;
  const unsigned col = blockIdx.z;
  const unsigned half_log_count = log_count >> 1;
  const unsigned shift = 32 - half_log_count;
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
    const unsigned ry = __brev(y_src + i) >> shift;
    const T value = src.get(ry * stride + x_src, col);
    tile[is_reverse][idx][tid_x] = value;
  }
  __syncthreads();
#pragma unroll
  for (int i = 0; i < TILE_DIM; i += BLOCK_ROWS) {
    const unsigned idx = tid_y + i;
    const unsigned ry = __brev(y_dst + i) >> shift;
    T value = tile[is_reverse][tid_x >> LOG_CHUNK_SIZE][idx << LOG_CHUNK_SIZE | (tid_x & (CHUNK_SIZE - 1))];
    dst.set(ry * stride + x_dst, col, value);
  }
}

#define BIT_REVERSE(name, arg_t, lcs)                                                                                                                          \
  EXTERN __launch_bounds__(128) __global__ void ab_bit_reverse_##name##_kernel(const matrix_getter<arg_t, ld_modifier::cs> src,                                \
                                                                               const matrix_setter<arg_t, st_modifier::cs> dst, const unsigned log_count) {    \
    bit_reverse<arg_t, lcs>(src, dst, log_count);                                                                                                              \
  }

BIT_REVERSE(bf, bf, 0);
BIT_REVERSE(e2, e2, 0);
BIT_REVERSE(e4, e4, 0);
BIT_REVERSE(dg, e4, 1);

} // namespace airbender::ops
