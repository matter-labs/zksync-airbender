#include "../common.cuh"
#include "../primitives/field.cuh"
#include "../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ops {

template <typename T, unsigned LOG_TILE_DIM>
DEVICE_FORCEINLINE void transpose(const matrix_getter<T, ld_modifier::cs> src, const matrix_setter<T, st_modifier::cs> dst, const unsigned src_rows,
                                  const unsigned src_cols) {
  constexpr unsigned LOG_BLOCK_SIZE = 7;
  constexpr unsigned TILE_DIM = 1u << LOG_TILE_DIM;
  constexpr unsigned LOG_TILES_COUNT = LOG_BLOCK_SIZE - LOG_TILE_DIM;
  constexpr unsigned TILES_COUNT = 1u << LOG_TILES_COUNT;
  __shared__ T tiles[TILES_COUNT][TILE_DIM][TILE_DIM];
  const unsigned tid = threadIdx.x;
  const unsigned block_tile_index = threadIdx.y;
  auto tile = tiles[block_tile_index];
  const unsigned flat_tile_index = blockIdx.x * blockDim.y + block_tile_index;
  const unsigned src_tiles_per_row = (src_cols + TILE_DIM - 1) / TILE_DIM;
  const unsigned src_tile_row_offset = flat_tile_index / src_tiles_per_row * TILE_DIM;
  const unsigned src_tile_col_offset = flat_tile_index % src_tiles_per_row * TILE_DIM;
  const unsigned dst_tile_row_offset = src_tile_col_offset;
  const unsigned dst_tile_col_offset = src_tile_row_offset;
  const unsigned src_row = src_tile_row_offset + tid;
  const unsigned dst_row = dst_tile_row_offset + tid;
#pragma unroll
  for (unsigned i = 0; i < TILE_DIM; i++) {
    const unsigned src_col = src_tile_col_offset + i;
    const unsigned row_swizzled = tid ^ i;
    if (src_row < src_rows && src_col < src_cols)
      tile[i][row_swizzled] = src.get(src_row, src_col);
  }
  if (LOG_TILE_DIM <= 5)
    __syncwarp();
  else
    __syncthreads();
#pragma unroll
  for (unsigned i = 0; i < TILE_DIM; i++) {
    const unsigned dst_col = dst_tile_col_offset + i;
    const unsigned row_swizzled = tid ^ i;
    if (dst_row < src_cols && dst_col < src_rows)
      dst.set(dst_row, dst_col, tile[tid][row_swizzled]);
  }
}

#define TRANSPOSE_KERNEL(arg_t, log_tile_dim)                                                                                                                  \
  EXTERN __global__ void ab_transpose_##arg_t##_kernel(const matrix_getter<arg_t, ld_modifier::cs> src, const matrix_setter<arg_t, st_modifier::cs> dst,       \
                                                       const unsigned src_rows, const unsigned src_cols) {                                                     \
    transpose<arg_t, log_tile_dim>(src, dst, src_rows, src_cols);                                                                                              \
  }

TRANSPOSE_KERNEL(bf, 5);
TRANSPOSE_KERNEL(e2, 4);
TRANSPOSE_KERNEL(e4, 3);
TRANSPOSE_KERNEL(e6, 3);

} // namespace airbender::ops
