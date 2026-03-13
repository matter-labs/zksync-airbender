#include "complex.cuh"
// #include "context.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ops::complex {

struct __align__(32) dg {
  bf values[8];
};

template <typename F>
DEVICE_FORCEINLINE void get_powers(const F &base, const unsigned offset, const bool bit_reverse, vector_setter<F, st_modifier::cs> result,
                                   const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  const unsigned power = (bit_reverse ? __brev(gid) : gid) + offset;
  const F value = F::pow(base, power);
  result.set(gid, value);
}

#define GET_POWERS_BY_VAL_KERNEL(arg_t)                                                                                                                        \
  EXTERN __global__ void ab_get_powers_by_val_##arg_t##_kernel(const arg_t base, const unsigned offset, const bool bit_reverse,                                \
                                                               vector_setter<arg_t, st_modifier::cs> result, const unsigned count) {                           \
    get_powers(base, offset, bit_reverse, result, count);                                                                                                      \
  }
#define GET_POWERS_BY_REF_KERNEL(arg_t)                                                                                                                        \
  EXTERN __global__ void ab_get_powers_by_ref_##arg_t##_kernel(const arg_t *base, const unsigned offset, const bool bit_reverse,                               \
                                                               vector_setter<arg_t, st_modifier::cs> result, const unsigned count) {                           \
    get_powers(*base, offset, bit_reverse, result, count);                                                                                                     \
  }

GET_POWERS_BY_VAL_KERNEL(bf);
GET_POWERS_BY_VAL_KERNEL(e2);
GET_POWERS_BY_VAL_KERNEL(e4);
GET_POWERS_BY_VAL_KERNEL(e6);
GET_POWERS_BY_REF_KERNEL(bf);
GET_POWERS_BY_REF_KERNEL(e2);
GET_POWERS_BY_REF_KERNEL(e4);
GET_POWERS_BY_REF_KERNEL(e6);

template <typename T, typename GETTER, typename SETTER> DEVICE_FORCEINLINE void batch_inv_impl(GETTER src, SETTER dst, const unsigned count) {
  constexpr unsigned INV_BATCH = InvBatch<T>::INV_BATCH;

  // ints for indexing because some bounds checks count down and check if an index drops below 0
  const int gid = static_cast<int>(blockIdx.x * blockDim.x + threadIdx.x);

  // If count < grid size, the kernel is inefficient no matter what (because each thread processes just one element)
  // but we should still bail out if a thread has no assigned elems at all.
  if (gid >= count)
    return;

  const int grid_size = static_cast<int>(blockDim.x * gridDim.x);

  T inputs[INV_BATCH];
  T outputs[INV_BATCH];

  int runtime_batch_size = 0;
  int g = gid;
#pragma unroll
  for (int i = 0; i < INV_BATCH; i++, g += grid_size)
    if (g < count) {
      inputs[i] = src.get(g);
      runtime_batch_size++;
    }

  if (runtime_batch_size < INV_BATCH) {
    batch_inv_registers<T, INV_BATCH, false>(inputs, outputs, runtime_batch_size);
  } else {
    batch_inv_registers<T, INV_BATCH, true>(inputs, outputs, runtime_batch_size);
  }

  g -= grid_size;
#pragma unroll
  for (int i = INV_BATCH - 1; i >= 0; --i, g -= grid_size)
    if (i < runtime_batch_size)
      dst.set(g, outputs[i]);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_batch_inv_bf_kernel(const bf_vector_getter<ld_modifier::cs> src, const bf_vector_setter<st_modifier::cs> dst, const unsigned count) {
  batch_inv_impl<bf>(src, dst, count);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_batch_inv_e2_kernel(const e2_vector_getter<ld_modifier::cs> src, const e2_vector_setter<st_modifier::cs> dst, const unsigned count) {
  batch_inv_impl<e2>(src, dst, count);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_batch_inv_e4_kernel(const e4_vector_getter<ld_modifier::cs> src, const e4_vector_setter<st_modifier::cs> dst, const unsigned count) {
  batch_inv_impl<e4>(src, dst, count);
}

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

// EXTERN __global__ void ab_fold_kernel(const e4 *challenge, const e4 *src, e4 *dst, const unsigned root_offset, const unsigned log_count) {
//   const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
//   if (gid >= 1u << log_count)
//     return;
//   const e4 even = src[2 * gid];
//   const e4 odd = src[2 * gid + 1];
//   const e4 sum = even + odd;
//   e4 diff = even - odd;
//   const unsigned root_index = __brev(gid + root_offset) >> (32 - CIRCLE_GROUP_LOG_ORDER + 1);
//   const e2 root = get_power_of_w(root_index, true);
//   diff *= root;
//   diff *= *challenge;
//   const e4 result = sum + diff;
//   dst[gid] = result;
// }

template <typename E> struct gkr_ext_initial_source {
  const E *start;
  size_t next_layer_size;
};

template <typename E> struct gkr_ext_continuing_source {
  const E *previous_layer_start;
  E *this_layer_start;
  size_t this_layer_size;
  size_t next_layer_size;
  E folding_challenge;
  bool first_access;
};

template <typename E>
DEVICE_FORCEINLINE E gkr_get_initial_value(const gkr_ext_initial_source<E> &source, const unsigned index) {
  return load<E, ld_modifier::cs>(source.start, index);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_continuing_value(const gkr_ext_continuing_source<E> &source, const unsigned index) {
  if (!source.first_access)
    return load<E, ld_modifier::cs>(source.this_layer_start, index);

  const E f0 = load<E, ld_modifier::cs>(source.previous_layer_start, index);
  const E f1 = load<E, ld_modifier::cs>(source.previous_layer_start, source.this_layer_size + index);
  const E diff = E::sub(f1, f0);
  const E folded = E::add(f0, E::mul(source.folding_challenge, diff));
  store<E, st_modifier::cs>(source.this_layer_start, folded, index);
  return folded;
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_initial_delta(const gkr_ext_initial_source<E> &source, const unsigned index) {
  const E f0 = gkr_get_initial_value(source, index);
  const E f1 = gkr_get_initial_value(source, source.next_layer_size + index);
  return E::sub(f1, f0);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_get_continuing_points(
    const gkr_ext_continuing_source<E> &source, const unsigned index, E &f0, E &f1_or_delta) {
  f0 = gkr_get_continuing_value(source, index);
  const E f1 = gkr_get_continuing_value(source, source.next_layer_size + index);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E>
DEVICE_FORCEINLINE void gkr_store_contribution(E *dst, const unsigned index, const E c0, const E c1) {
  store<E, st_modifier::cs>(dst, c0, 2 * index);
  store<E, st_modifier::cs>(dst, c1, 2 * index + 1);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_round0(
    const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E batch_challenge, E *contributions,
    const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  const E output_value = gkr_get_initial_value(outputs[0], gid);
  const E delta_even = gkr_get_initial_delta(inputs[0], even_index);
  const E delta_odd = gkr_get_initial_delta(inputs[0], odd_index);

  const E c0 = E::mul(batch_challenge, output_value);
  const E c1 = E::mul(batch_challenge, E::mul(delta_even, delta_odd));
  gkr_store_contribution(contributions, gid, c0, c1);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_round0(
    const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E batch_challenge_0, const E batch_challenge_1,
    E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  const E output_num = gkr_get_initial_value(outputs[0], gid);
  const E output_den = gkr_get_initial_value(outputs[1], gid);

  const E a = gkr_get_initial_delta(inputs[0], even_index);
  const E b = gkr_get_initial_delta(inputs[1], even_index);
  const E c = gkr_get_initial_delta(inputs[0], odd_index);
  const E d = gkr_get_initial_delta(inputs[1], odd_index);

  const E num = E::add(E::mul(a, d), E::mul(c, b));
  const E den = E::mul(b, d);

  const E c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
  const E c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
  gkr_store_contribution(contributions, gid, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_pairwise_continuation(
    const gkr_ext_continuing_source<E> *inputs, const E batch_challenge, E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E even_f0;
  E even_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], even_index, even_f0, even_f1_or_delta);

  E odd_f0;
  E odd_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], odd_index, odd_f0, odd_f1_or_delta);

  const E c0 = E::mul(batch_challenge, E::mul(even_f0, odd_f0));
  const E c1 = E::mul(batch_challenge, E::mul(even_f1_or_delta, odd_f1_or_delta));
  gkr_store_contribution(contributions, gid, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_lookup_continuation(
    const gkr_ext_continuing_source<E> *inputs, const E batch_challenge_0, const E batch_challenge_1, E *contributions,
    const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E a0;
  E a1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], even_index, a0, a1);
  E b0;
  E b1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], even_index, b0, b1);
  E c0;
  E c1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], odd_index, c0, c1);
  E d0;
  E d1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], odd_index, d0, d1);

  const E num0 = E::add(E::mul(a0, d0), E::mul(c0, b0));
  const E den0 = E::mul(b0, d0);
  const E num1 = E::add(E::mul(a1, d1), E::mul(c1, b1));
  const E den1 = E::mul(b1, d1);

  const E out0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
  const E out1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
  gkr_store_contribution(contributions, gid, out0, out1);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_weight_contributions(
    const E *contributions, const unsigned kernel_count, const E *eq_values, E *weighted_rows, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E acc0 = E::ZERO();
  E acc1 = E::ZERO();
  for (unsigned kernel_idx = 0; kernel_idx < kernel_count; ++kernel_idx) {
    const unsigned base = kernel_idx * acc_size * 2 + gid * 2;
    acc0 = E::add(acc0, load<E, ld_modifier::cs>(contributions, base));
    acc1 = E::add(acc1, load<E, ld_modifier::cs>(contributions, base + 1));
  }
  const E eq = load<E, ld_modifier::cs>(eq_values, gid);
  store<E, st_modifier::cs>(weighted_rows, E::mul(acc0, eq), gid);
  store<E, st_modifier::cs>(weighted_rows, E::mul(acc1, eq), acc_size + gid);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_values(
    const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count, E *eq_values, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E acc = E::ONE();
  for (unsigned i = 0; i < challenge_count; ++i) {
    const E challenge = load<E, ld_modifier::cs>(claim_point, challenge_offset + i);
    const bool bit = ((gid >> (challenge_count - 1 - i)) & 1u) != 0;
    const E term = bit ? challenge : E::sub(E::ONE(), challenge);
    acc = E::mul(acc, term);
  }

  store<E, st_modifier::cs>(eq_values, acc, gid);
}

#define GKR_DIM_REDUCING_KERNELS(arg_t)                                                                                                                       \
  EXTERN __global__ void ab_gkr_dim_reducing_pairwise_round0_##arg_t##_kernel(                                                                                \
      const gkr_ext_initial_source<arg_t> *inputs, const gkr_ext_initial_source<arg_t> *outputs, const arg_t batch_challenge, arg_t *contributions,          \
      const unsigned acc_size) {                                                                                                                               \
    gkr_pairwise_round0(inputs, outputs, batch_challenge, contributions, acc_size);                                                                           \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_lookup_round0_##arg_t##_kernel(                                                                                  \
      const gkr_ext_initial_source<arg_t> *inputs, const gkr_ext_initial_source<arg_t> *outputs, const arg_t batch_challenge_0,                              \
      const arg_t batch_challenge_1, arg_t *contributions, const unsigned acc_size) {                                                                         \
    gkr_lookup_round0(inputs, outputs, batch_challenge_0, batch_challenge_1, contributions, acc_size);                                                       \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_pairwise_continuation_##arg_t##_kernel(                                                                          \
      const gkr_ext_continuing_source<arg_t> *inputs, const arg_t batch_challenge, const bool explicit_form, arg_t *contributions,                            \
      const unsigned acc_size) {                                                                                                                               \
    if (explicit_form)                                                                                                                                         \
      gkr_pairwise_continuation<arg_t, true>(inputs, batch_challenge, contributions, acc_size);                                                               \
    else                                                                                                                                                       \
      gkr_pairwise_continuation<arg_t, false>(inputs, batch_challenge, contributions, acc_size);                                                              \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_lookup_continuation_##arg_t##_kernel(                                                                            \
      const gkr_ext_continuing_source<arg_t> *inputs, const arg_t batch_challenge_0, const arg_t batch_challenge_1, const bool explicit_form,                \
      arg_t *contributions, const unsigned acc_size) {                                                                                                         \
    if (explicit_form)                                                                                                                                         \
      gkr_lookup_continuation<arg_t, true>(inputs, batch_challenge_0, batch_challenge_1, contributions, acc_size);                                           \
    else                                                                                                                                                       \
      gkr_lookup_continuation<arg_t, false>(inputs, batch_challenge_0, batch_challenge_1, contributions, acc_size);                                          \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_build_eq_##arg_t##_kernel(                                                                                       \
      const arg_t *claim_point, const unsigned challenge_offset, const unsigned challenge_count, arg_t *eq_values, const unsigned acc_size) {                 \
    gkr_build_eq_values(claim_point, challenge_offset, challenge_count, eq_values, acc_size);                                                                 \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_weight_contributions_##arg_t##_kernel(                                                                           \
      const arg_t *contributions, const unsigned kernel_count, const arg_t *eq_values, arg_t *weighted_rows, const unsigned acc_size) {                       \
    gkr_weight_contributions(contributions, kernel_count, eq_values, weighted_rows, acc_size);                                                                \
  }

GKR_DIM_REDUCING_KERNELS(e2);
GKR_DIM_REDUCING_KERNELS(e4);
GKR_DIM_REDUCING_KERNELS(e6);

} // namespace airbender::ops::complex
