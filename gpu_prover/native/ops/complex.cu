#include "complex.cuh"
// #include "context.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::ops::complex {

struct __align__(32) dg { bf values[8]; };

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

EXTERN __global__ void ab_serialize_whir_e4_columns_kernel(const e4 *src, bf *dst, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  const e4 value = load<e4, ld_modifier::cs>(src, gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(0), gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(1), count + gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(2), 2 * count + gid);
  store<bf, st_modifier::cs>(dst, value.base_coefficient_from_flat_idx(3), 3 * count + gid);
}

EXTERN __global__ void ab_deserialize_whir_e4_columns_kernel(const bf *src, e4 *dst, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  const bf coeffs[4] = {
      load<bf, ld_modifier::cs>(src, gid),
      load<bf, ld_modifier::cs>(src, count + gid),
      load<bf, ld_modifier::cs>(src, 2 * count + gid),
      load<bf, ld_modifier::cs>(src, 3 * count + gid),
  };
  store<e4, st_modifier::cs>(dst, e4(coeffs), gid);
}

EXTERN __global__ void ab_accumulate_whir_base_columns_e4_kernel(const bf *values, const unsigned stride, const e4 *weights, const unsigned cols, e4 *result,
                                                                 const unsigned rows) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= rows)
    return;

  e4 acc = load<e4, ld_modifier::cs>(result, gid);
  for (unsigned col = 0; col < cols; ++col) {
    const bf value = load<bf, ld_modifier::cs>(values, col * stride + gid);
    const e4 weight = load<e4, ld_modifier::cs>(weights, col);
    acc = e4::add(acc, e4::mul(weight, value));
  }
  store<e4, st_modifier::cs>(result, acc, gid);
}

EXTERN __global__ void ab_whir_fold_monomial_e4_kernel(const e4 *src, const e4 *challenge, e4 *dst, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 c0 = load<e4, ld_modifier::cs>(src, 2 * gid);
  const e4 c1 = load<e4, ld_modifier::cs>(src, 2 * gid + 1);
  const e4 folded = e4::add(c0, e4::mul(c1, *challenge));
  store<e4, st_modifier::cs>(dst, folded, gid);
}

EXTERN __global__ void ab_whir_fold_split_half_e4_kernel(e4 *values, const e4 *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const e4 a = load<e4, ld_modifier::cs>(values, gid);
  const e4 b = load<e4, ld_modifier::cs>(values, half_len + gid);
  const e4 diff = e4::sub(b, a);
  const e4 folded = e4::add(a, e4::mul(*challenge, diff));
  store<e4, st_modifier::cs>(values, folded, gid);
}

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

EXTERN __global__ void ab_pack_rows_for_whir_leaves_bf_kernel(const matrix_getter<bf, ld_modifier::cs> src, const matrix_setter<bf, st_modifier::cs> dst,
                                                              const unsigned log_values_per_leaf, const unsigned dst_rows_per_slot, const unsigned row_stride,
                                                              const unsigned row_offset, const unsigned src_cols) {
  const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
  if (row >= dst_rows_per_slot)
    return;
  const unsigned col = blockIdx.y * blockDim.y + threadIdx.y;
  const unsigned dst_cols = src_cols << log_values_per_leaf;
  if (col >= dst_cols)
    return;
  const unsigned value_slot = col / src_cols;
  const unsigned coeff_col = col % src_cols;
  const unsigned src_row = row + bitreverse_low_bits(value_slot, log_values_per_leaf) * dst_rows_per_slot;
  const unsigned dst_row = row * row_stride + row_offset;
  dst.set(dst_row, col, src.get(src_row, coeff_col));
}

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

template <typename B> struct gkr_base_initial_source {
  const B *start;
  size_t next_layer_size;
};

template <typename B, typename E> struct gkr_base_after_one_source {
  size_t base_layer_half_size;
  size_t next_layer_size;
  const B *base_input_start;
};

template <typename B, typename E> struct gkr_base_after_two_source {
  const B *base_input_start;
  E *this_layer_cache_start;
  size_t base_layer_half_size;
  size_t base_quarter_size;
  size_t next_layer_size;
  bool first_access;
};

template <typename E> struct gkr_ext_continuing_source {
  const E *previous_layer_start;
  E *this_layer_start;
  size_t this_layer_size;
  size_t next_layer_size;
  bool first_access;
};

template <typename E> struct gkr_main_constraint_quadratic_term {
  u32 lhs;
  u32 rhs;
  E challenge;
};

template <typename E> struct gkr_main_constraint_linear_term {
  u32 input;
  E challenge;
};

enum gkr_main_kernel_kind : u32 {
  GKR_MAIN_BASE_COPY = 0,
  GKR_MAIN_EXT_COPY = 1,
  GKR_MAIN_PRODUCT = 2,
  GKR_MAIN_MASK_IDENTITY = 3,
  GKR_MAIN_LOOKUP_PAIR = 4,
  GKR_MAIN_LOOKUP_BASE_PAIR = 5,
  GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY = 6,
  GKR_MAIN_LOOKUP_UNBALANCED = 7,
  GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP = 8,
  GKR_MAIN_ENFORCE_CONSTRAINTS = 9,
};

static constexpr unsigned GKR_FORWARD_MAX_GATES_PER_LAYER = 64;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_MAX_INPUTS = 5;
static constexpr unsigned GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS = 10;

enum gkr_forward_gate_kind : u32 {
  GKR_FORWARD_NO_OP = 0,
  GKR_FORWARD_PRODUCT = 1,
  GKR_FORWARD_MASK_IDENTITY = 2,
  GKR_FORWARD_LOOKUP_PAIR = 3,
  GKR_FORWARD_LOOKUP_WITH_CACHED_DENS_AND_SETUP = 4,
  GKR_FORWARD_LOOKUP_BASE_PAIR = 5,
  GKR_FORWARD_LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE = 6,
  GKR_FORWARD_LOOKUP_UNBALANCED_BASE = 7,
  GKR_FORWARD_LOOKUP_UNBALANCED_EXTENSION = 8,
};

struct gkr_forward_no_op_descriptor {
  size_t reserved;
};

template <typename E> struct gkr_forward_product_descriptor {
  const E *lhs;
  const E *rhs;
  E *dst;
};

template <typename E> struct gkr_forward_mask_identity_descriptor {
  const E *input;
  const bf *mask;
  E *dst;
};

template <typename E> struct gkr_forward_lookup_pair_descriptor {
  const E *a;
  const E *b;
  const E *c;
  const E *d;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_with_cached_dens_and_setup_descriptor {
  const bf *a;
  const E *b;
  const bf *c;
  const E *d;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_base_pair_descriptor {
  const bf *lhs;
  const bf *rhs;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_base_minus_multiplicity_by_base_descriptor {
  const bf *b;
  const bf *c;
  const bf *d;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_unbalanced_base_descriptor {
  const E *a;
  const E *b;
  const bf *remainder;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_unbalanced_extension_descriptor {
  const E *a;
  const E *b;
  const E *remainder;
  E *num;
  E *den;
};

template <typename E> union gkr_forward_gate_payload {
  gkr_forward_no_op_descriptor no_op;
  gkr_forward_product_descriptor<E> product;
  gkr_forward_mask_identity_descriptor<E> mask_identity;
  gkr_forward_lookup_pair_descriptor<E> lookup_pair;
  gkr_forward_lookup_with_cached_dens_and_setup_descriptor<E> lookup_with_cached_dens_and_setup;
  gkr_forward_lookup_base_pair_descriptor<E> lookup_base_pair;
  gkr_forward_lookup_base_minus_multiplicity_by_base_descriptor<E> lookup_base_minus_multiplicity_by_base;
  gkr_forward_lookup_unbalanced_base_descriptor<E> lookup_unbalanced_base;
  gkr_forward_lookup_unbalanced_extension_descriptor<E> lookup_unbalanced_extension;
};

template <typename E> struct gkr_forward_gate_descriptor {
  u32 kind;
  u32 reserved;
  gkr_forward_gate_payload<E> payload;
};

template <typename E> struct gkr_forward_layer_batch {
  u32 gate_count;
  u32 reserved;
  const E *lookup_additive_challenge;
  gkr_forward_gate_descriptor<E> descriptors[GKR_FORWARD_MAX_GATES_PER_LAYER];
};

enum gkr_dim_reducing_forward_input_kind : u32 {
  GKR_DIM_REDUCING_FORWARD_NO_OP = 0,
  GKR_DIM_REDUCING_FORWARD_PAIRWISE_PRODUCT = 1,
  GKR_DIM_REDUCING_FORWARD_LOOKUP_PAIR = 2,
};

struct gkr_dim_reducing_forward_no_op_descriptor {
  size_t reserved;
};

template <typename E> struct gkr_dim_reducing_forward_pairwise_product_descriptor {
  const E *input;
  E *output;
};

template <typename E> struct gkr_dim_reducing_forward_lookup_pair_descriptor {
  const E *num;
  const E *den;
  E *output_num;
  E *output_den;
};

template <typename E> union gkr_dim_reducing_forward_input_payload {
  gkr_dim_reducing_forward_no_op_descriptor no_op;
  gkr_dim_reducing_forward_pairwise_product_descriptor<E> pairwise_product;
  gkr_dim_reducing_forward_lookup_pair_descriptor<E> lookup_pair;
};

template <typename E> struct gkr_dim_reducing_forward_input_descriptor {
  u32 kind;
  u32 reserved;
  gkr_dim_reducing_forward_input_payload<E> payload;
};

template <typename E> struct gkr_dim_reducing_forward_batch {
  u32 input_count;
  u32 reserved;
  gkr_dim_reducing_forward_input_descriptor<E> descriptors[GKR_DIM_REDUCING_FORWARD_MAX_INPUTS];
};

struct gkr_forward_setup_generic_lookup_descriptor {
  const bf *input;
};

template <typename E> struct gkr_forward_setup_generic_lookup_batch {
  u32 column_count;
  u32 reserved;
  const E *alpha_powers;
  E *output;
  gkr_forward_setup_generic_lookup_descriptor descriptors[GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
};

constexpr unsigned GKR_FORWARD_CACHE_MAX_RELATIONS = 20;
constexpr unsigned GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS = 6;

enum gkr_forward_cache_kind : u32 {
  GKR_FORWARD_CACHE_EMPTY = 0,
  GKR_FORWARD_CACHE_SINGLE_COLUMN_LOOKUP = 1,
  GKR_FORWARD_CACHE_VECTORIZED_LOOKUP = 2,
  GKR_FORWARD_CACHE_VECTORIZED_LOOKUP_SETUP = 3,
  GKR_FORWARD_CACHE_MEMORY_TUPLE = 4,
};

enum gkr_forward_cache_address_space_kind : u32 {
  GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY = 0,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT = 1,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_IS = 2,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT = 3,
};

template <typename E> struct gkr_forward_cache_descriptor {
  gkr_forward_cache_kind kind;
  gkr_forward_cache_address_space_kind address_space_kind;
  const u32 *mapping;
  const bf *setup_values;
  const E *generic_lookup;
  bf *base_output;
  E *ext_output;
  u32 generic_lookup_len;
  const bf *address_space_ptr;
  bf address_space_constant;
  E constant_term;
  const bf *linear_inputs[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
  E linear_challenges[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
};

template <typename E> struct gkr_forward_cache_batch {
  u32 count;
  gkr_forward_cache_descriptor<E> descriptors[GKR_FORWARD_CACHE_MAX_RELATIONS];
};

template <typename E> DEVICE_FORCEINLINE E gkr_lift_base(const bf value) { return E::mul(E::ONE(), value); }

template <typename E> DEVICE_FORCEINLINE void gkr_forward_cache_memory_tuple(const gkr_forward_cache_descriptor<E> &descriptor, const unsigned gid) {
  E value = descriptor.constant_term;
  switch (descriptor.address_space_kind) {
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT:
    value = E::add(value, gkr_lift_base<E>(descriptor.address_space_constant));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_IS:
    value = E::add(value, gkr_lift_base<E>(load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid)));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT:
    value = E::add(value, E::sub(E::ONE(), gkr_lift_base<E>(load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid))));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY:
    break;
  }

#pragma unroll
  for (unsigned term = 0; term < GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS; ++term) {
    if (descriptor.linear_inputs[term] == nullptr)
      continue;
    const bf input = load<bf, ld_modifier::cs>(descriptor.linear_inputs[term], gid);
    value = E::add(value, E::mul(descriptor.linear_challenges[term], input));
  }

  store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
}

template <typename E> DEVICE_FORCEINLINE void gkr_forward_cache(const gkr_forward_cache_batch<E> &batch, const unsigned trace_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= trace_len)
    return;

#pragma unroll
  for (unsigned relation_idx = 0; relation_idx < GKR_FORWARD_CACHE_MAX_RELATIONS; ++relation_idx) {
    if (relation_idx >= batch.count)
      return;

    const auto &descriptor = batch.descriptors[relation_idx];
    switch (descriptor.kind) {
    case GKR_FORWARD_CACHE_SINGLE_COLUMN_LOOKUP: {
      const unsigned mapping = descriptor.mapping[gid];
      const bf value = load<bf, ld_modifier::cs>(descriptor.setup_values, mapping);
      store<bf, st_modifier::cs>(descriptor.base_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_VECTORIZED_LOOKUP: {
      const unsigned mapping = descriptor.mapping[gid];
      const E value = load<E, ld_modifier::cs>(descriptor.generic_lookup, mapping);
      store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_VECTORIZED_LOOKUP_SETUP: {
      const E value = gid < descriptor.generic_lookup_len ? load<E, ld_modifier::cs>(descriptor.generic_lookup, gid) : E::ZERO();
      store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_MEMORY_TUPLE:
      gkr_forward_cache_memory_tuple(descriptor, gid);
      break;
    case GKR_FORWARD_CACHE_EMPTY:
      return;
    }
  }
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_base_value(const gkr_base_initial_source<bf> &source, const unsigned index) {
  return gkr_lift_base<E>(load<bf, ld_modifier::cs>(source.start, index));
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_base_delta(const gkr_base_initial_source<bf> &source, const unsigned index) {
  const bf f0 = load<bf, ld_modifier::cs>(source.start, index);
  const bf f1 = load<bf, ld_modifier::cs>(source.start, source.next_layer_size + index);
  return gkr_lift_base<E>(bf::sub(f1, f0));
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_value(const gkr_ext_initial_source<E> &source, const unsigned index) {
  return load<E, ld_modifier::cs>(source.start, index);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_continuing_value(const gkr_ext_continuing_source<E> &source, const E folding_challenge, const unsigned index) {
  if (!source.first_access)
    return load<E, ld_modifier::cs>(source.this_layer_start, index);

  const E f0 = load<E, ld_modifier::cs>(source.previous_layer_start, index);
  const E f1 = load<E, ld_modifier::cs>(source.previous_layer_start, source.this_layer_size + index);
  const E diff = E::sub(f1, f0);
  const E folded = E::add(f0, E::mul(folding_challenge, diff));
  store<E, st_modifier::cs>(source.this_layer_start, folded, index);
  return folded;
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_delta(const gkr_ext_initial_source<E> &source, const unsigned index) {
  const E f0 = gkr_get_initial_value(source, index);
  const E f1 = gkr_get_initial_value(source, source.next_layer_size + index);
  return E::sub(f1, f0);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_base_after_one_value(const gkr_base_after_one_source<bf, E> &source, const E first_folding_challenge, const unsigned index) {
  const bf f0 = load<bf, ld_modifier::cs>(source.base_input_start, index);
  const bf f1 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_layer_half_size + index);
  const bf diff = bf::sub(f1, f0);
  return E::add(E::mul(first_folding_challenge, diff), f0);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_get_base_after_one_points(const gkr_base_after_one_source<bf, E> &source, const E first_folding_challenge, const unsigned index,
                                                      E &f0, E &f1_or_delta) {
  f0 = gkr_get_base_after_one_value(source, first_folding_challenge, index);
  const E f1 = gkr_get_base_after_one_value(source, first_folding_challenge, source.next_layer_size + index);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_base_after_two_value(const gkr_base_after_two_source<bf, E> &source, const E first_folding_challenge,
                                                  const E second_folding_challenge, const unsigned index) {
  if (!source.first_access)
    return load<E, ld_modifier::cs>(source.this_layer_cache_start, index);

  const bf f00 = load<bf, ld_modifier::cs>(source.base_input_start, index);
  const bf f01 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_layer_half_size + index);
  const bf f10 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_quarter_size + index);
  const bf f11 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_layer_half_size + source.base_quarter_size + index);

  const bf c01 = bf::sub(f01, f00);
  const bf c10 = bf::sub(f10, f00);
  bf c11 = f00;
  c11 = bf::sub(c11, f01);
  c11 = bf::sub(c11, f10);
  c11 = bf::add(c11, f11);

  E combined_challenges = E::mul(first_folding_challenge, second_folding_challenge);
  E result = E::mul(first_folding_challenge, c01);
  result = E::add(result, E::mul(second_folding_challenge, c10));
  result = E::add(result, E::mul(combined_challenges, c11));
  result = E::add(result, f00);

  store<E, st_modifier::cs>(source.this_layer_cache_start, result, index);
  return result;
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_get_base_after_two_points(const gkr_base_after_two_source<bf, E> &source, const E first_folding_challenge,
                                                      const E second_folding_challenge, const unsigned index, E &f0, E &f1_or_delta) {
  f0 = gkr_get_base_after_two_value(source, first_folding_challenge, second_folding_challenge, index);
  const E f1 = gkr_get_base_after_two_value(source, first_folding_challenge, second_folding_challenge, source.next_layer_size + index);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_get_continuing_points(const gkr_ext_continuing_source<E> &source, const E folding_challenge, const unsigned index, E &f0,
                                                  E &f1_or_delta) {
  f0 = gkr_get_continuing_value(source, folding_challenge, index);
  const E f1 = gkr_get_continuing_value(source, folding_challenge, source.next_layer_size + index);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E> DEVICE_FORCEINLINE void gkr_accumulate_contribution(E *dst, const unsigned index, const unsigned acc_size, const E c0, const E c1) {
  const E prev0 = load<E, ld_modifier::cs>(dst, index);
  const E prev1 = load<E, ld_modifier::cs>(dst, acc_size + index);
  store<E, st_modifier::cs>(dst, E::add(prev0, c0), index);
  store<E, st_modifier::cs>(dst, E::add(prev1, c1), acc_size + index);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_round0(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                            E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E batch_challenge = batch_challenges[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  const E output_value = gkr_get_initial_value(outputs[0], gid);
  const E delta_even = gkr_get_initial_delta(inputs[0], even_index);
  const E delta_odd = gkr_get_initial_delta(inputs[0], odd_index);

  const E c0 = E::mul(batch_challenge, output_value);
  const E c1 = E::mul(batch_challenge, E::mul(delta_even, delta_odd));
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_round0(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                          E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];

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
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_pairwise_continuation(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                  E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E current_folding_challenge = folding_challenge[0];
  const E batch_challenge = batch_challenges[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E even_f0;
  E even_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, even_index, even_f0, even_f1_or_delta);

  E odd_f0;
  E odd_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, odd_index, odd_f0, odd_f1_or_delta);

  const E c0 = E::mul(batch_challenge, E::mul(even_f0, odd_f0));
  const E c1 = E::mul(batch_challenge, E::mul(even_f1_or_delta, odd_f1_or_delta));
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_lookup_continuation(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E current_folding_challenge = folding_challenge[0];
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E a0;
  E a1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, even_index, a0, a1);
  E b0;
  E b1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], current_folding_challenge, even_index, b0, b1);
  E c0;
  E c1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, odd_index, c0, c1);
  E d0;
  E d1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], current_folding_challenge, odd_index, d0, d1);

  const E num0 = E::add(E::mul(a0, d0), E::mul(c0, b0));
  const E den0 = E::mul(b0, d0);
  const E num1 = E::add(E::mul(a1, d1), E::mul(c1, b1));
  const E den1 = E::mul(b1, d1);

  const E out0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
  const E out1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
  gkr_accumulate_contribution(contributions, gid, acc_size, out0, out1);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_values(const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count, E *eq_values,
                                            const unsigned acc_size) {
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

template <typename E> DEVICE_FORCEINLINE void gkr_eval_product(const E a, const E b, E &value) { value = E::mul(a, b); }

template <typename E> DEVICE_FORCEINLINE void gkr_eval_mask_identity(const E mask, const E value, E &result) {
  result = E::sub(value, E::ONE());
  result = E::mul(result, mask);
  result = E::add(result, E::ONE());
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_mask_identity_quadratic(const E mask, const E value, E &result) { result = E::mul(value, mask); }

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_pair(const E a, const E b, const E c, const E d, E &num, E &den) {
  num = E::add(E::mul(a, d), E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair(const E b, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::add(shifted_b, shifted_d);
  den = E::mul(shifted_b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair_quadratic(const E b, const E d, E &num, E &den) {
  num = E::ZERO();
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity(const E b, const E c, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::sub(shifted_d, E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity_quadratic(const E b, const E c, const E d, E &num, E &den) {
  (void)d;
  num = E::neg(E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced(const E d, const E a, const E b, const E gamma, E &num, E &den) {
  const E shifted_d = E::add(d, gamma);
  num = E::add(E::mul(a, shifted_d), b);
  den = E::mul(b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced_quadratic(const E d, const E a, const E b, E &num, E &den) {
  num = E::mul(d, a);
  den = E::mul(d, b);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup(const E a, const E b, const E c, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::sub(E::mul(a, shifted_d), E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup_quadratic(const E a, const E b, const E c, const E d, E &num, E &den) {
  num = E::sub(E::mul(a, d), E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_forward_layer(const gkr_forward_layer_batch<E> &batch, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  for (unsigned gate_idx = 0; gate_idx < batch.gate_count; ++gate_idx) {
    const auto descriptor = batch.descriptors[gate_idx];
    switch (descriptor.kind) {
    case GKR_FORWARD_NO_OP:
      break;
    case GKR_FORWARD_PRODUCT: {
      const auto params = descriptor.payload.product;
      const E lhs = load<E, ld_modifier::cs>(params.lhs, gid);
      const E rhs = load<E, ld_modifier::cs>(params.rhs, gid);
      E value;
      gkr_eval_product(lhs, rhs, value);
      store<E, st_modifier::cs>(params.dst, value, gid);
      break;
    }
    case GKR_FORWARD_MASK_IDENTITY: {
      const auto params = descriptor.payload.mask_identity;
      const E input = load<E, ld_modifier::cs>(params.input, gid);
      const E mask = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.mask, gid));
      E value;
      gkr_eval_mask_identity(mask, input, value);
      store<E, st_modifier::cs>(params.dst, value, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_PAIR: {
      const auto params = descriptor.payload.lookup_pair;
      const E a = load<E, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E c = load<E, ld_modifier::cs>(params.c, gid);
      const E d = load<E, ld_modifier::cs>(params.d, gid);
      E num;
      E den;
      gkr_eval_lookup_pair(a, b, c, d, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
      const auto params = descriptor.payload.lookup_with_cached_dens_and_setup;
      const E a = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.a, gid));
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E c = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.c, gid));
      const E d = load<E, ld_modifier::cs>(params.d, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_cached_dens_and_setup(a, b, c, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_BASE_PAIR: {
      const auto params = descriptor.payload.lookup_base_pair;
      const E b = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.lhs, gid));
      const E d = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.rhs, gid));
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_pair(b, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE: {
      const auto params = descriptor.payload.lookup_base_minus_multiplicity_by_base;
      const E b = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.b, gid));
      const E c = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.c, gid));
      const E d = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.d, gid));
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_minus_multiplicity(b, c, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_UNBALANCED_BASE: {
      const auto params = descriptor.payload.lookup_unbalanced_base;
      const E a = load<E, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E d = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.remainder, gid));
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_UNBALANCED_EXTENSION: {
      const auto params = descriptor.payload.lookup_unbalanced_extension;
      const E a = load<E, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E d = load<E, ld_modifier::cs>(params.remainder, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    default:
      return;
    }
  }
}

template <typename E> DEVICE_FORCEINLINE void gkr_dim_reducing_forward(const gkr_dim_reducing_forward_batch<E> &batch, const unsigned row_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= row_count)
    return;

  const unsigned even = gid * 2;
  const unsigned odd = even + 1;

#pragma unroll
  for (unsigned input_idx = 0; input_idx < GKR_DIM_REDUCING_FORWARD_MAX_INPUTS; ++input_idx) {
    if (input_idx >= batch.input_count)
      return;

    const auto descriptor = batch.descriptors[input_idx];
    switch (descriptor.kind) {
    case GKR_DIM_REDUCING_FORWARD_NO_OP:
      break;
    case GKR_DIM_REDUCING_FORWARD_PAIRWISE_PRODUCT: {
      const auto params = descriptor.payload.pairwise_product;
      const E lhs = load<E, ld_modifier::cs>(params.input, even);
      const E rhs = load<E, ld_modifier::cs>(params.input, odd);
      E value;
      gkr_eval_product(lhs, rhs, value);
      store<E, st_modifier::cs>(params.output, value, gid);
      break;
    }
    case GKR_DIM_REDUCING_FORWARD_LOOKUP_PAIR: {
      const auto params = descriptor.payload.lookup_pair;
      const E a = load<E, ld_modifier::cs>(params.num, even);
      const E b = load<E, ld_modifier::cs>(params.den, even);
      const E c = load<E, ld_modifier::cs>(params.num, odd);
      const E d = load<E, ld_modifier::cs>(params.den, odd);
      E num;
      E den;
      gkr_eval_lookup_pair(a, b, c, d, num, den);
      store<E, st_modifier::cs>(params.output_num, num, gid);
      store<E, st_modifier::cs>(params.output_den, den, gid);
      break;
    }
    default:
      return;
    }
  }
}

template <typename E>
DEVICE_FORCEINLINE void gkr_forward_setup_generic_lookup(const gkr_forward_setup_generic_lookup_batch<E> &batch, const unsigned row_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= row_count)
    return;

  E value = E::ZERO();

#pragma unroll
  for (unsigned column_idx = 0; column_idx < GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS; ++column_idx) {
    if (column_idx >= batch.column_count)
      break;

    const auto descriptor = batch.descriptors[column_idx];
    const bf input = load<bf, ld_modifier::cs>(descriptor.input, gid);
    const E alpha_power = load<E, ld_modifier::ca>(batch.alpha_powers, column_idx);
    value = E::add(value, E::mul(gkr_lift_base<E>(input), alpha_power));
  }

  store<E, st_modifier::cs>(batch.output, value, gid);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_eval_constraints_round0(const gkr_base_initial_source<bf> *base_inputs, const unsigned gid,
                                                 const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count) {
  E result = E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs = gkr_get_initial_base_delta<E>(base_inputs[term.lhs], gid);
    const E rhs = gkr_get_initial_base_delta<E>(base_inputs[term.rhs], gid);
    lhs = E::mul(lhs, rhs);
    lhs = E::mul(lhs, term.challenge);
    result = E::add(result, lhs);
  }

  return result;
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_eval_constraints_round1(const gkr_base_after_one_source<bf, E> *base_inputs, const E first_folding_challenge, const unsigned gid,
                                                    const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count,
                                                    const gkr_main_constraint_linear_term<E> *linear_terms, const unsigned linear_terms_count,
                                                    const E constant_offset, E &eval0, E &eval1) {
  eval0 = constant_offset;
  eval1 = EXPLICIT_FORM ? constant_offset : E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs0;
    E lhs1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], first_folding_challenge, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[term.rhs], first_folding_challenge, gid, rhs0, rhs1);

    eval0 = E::add(eval0, E::mul(E::mul(lhs0, rhs0), term.challenge));
    eval1 = E::add(eval1, E::mul(E::mul(lhs1, rhs1), term.challenge));
  }
  if constexpr (EXPLICIT_FORM) {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_one_points<E, true>(base_inputs[term.input], first_folding_challenge, gid, input0, input1);
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
      eval1 = E::add(eval1, E::mul(input1, term.challenge));
    }
  } else {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_one_points<E, false>(base_inputs[term.input], first_folding_challenge, gid, input0, input1);
      (void)input1;
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
    }
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_eval_constraints_round2(const gkr_base_after_two_source<bf, E> *base_inputs, const E first_folding_challenge,
                                                    const E second_folding_challenge, const unsigned gid,
                                                    const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count,
                                                    const gkr_main_constraint_linear_term<E> *linear_terms, const unsigned linear_terms_count,
                                                    const E constant_offset, E &eval0, E &eval1) {
  eval0 = constant_offset;
  eval1 = EXPLICIT_FORM ? constant_offset : E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs0;
    E lhs1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], first_folding_challenge, second_folding_challenge, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[term.rhs], first_folding_challenge, second_folding_challenge, gid, rhs0, rhs1);

    eval0 = E::add(eval0, E::mul(E::mul(lhs0, rhs0), term.challenge));
    eval1 = E::add(eval1, E::mul(E::mul(lhs1, rhs1), term.challenge));
  }
  if constexpr (EXPLICIT_FORM) {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_two_points<E, true>(base_inputs[term.input], first_folding_challenge, second_folding_challenge, gid, input0, input1);
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
      eval1 = E::add(eval1, E::mul(input1, term.challenge));
    }
  } else {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_two_points<E, false>(base_inputs[term.input], first_folding_challenge, second_folding_challenge, gid, input0, input1);
      (void)input1;
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
    }
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_eval_constraints_round3(const gkr_ext_continuing_source<E> *base_inputs, const E folding_challenge, const unsigned gid,
                                                    const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count,
                                                    const gkr_main_constraint_linear_term<E> *linear_terms, const unsigned linear_terms_count,
                                                    const E constant_offset, E &eval0, E &eval1) {
  eval0 = constant_offset;
  eval1 = EXPLICIT_FORM ? constant_offset : E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs0;
    E lhs1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], folding_challenge, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[term.rhs], folding_challenge, gid, rhs0, rhs1);

    eval0 = E::add(eval0, E::mul(E::mul(lhs0, rhs0), term.challenge));
    eval1 = E::add(eval1, E::mul(E::mul(lhs1, rhs1), term.challenge));
  }
  if constexpr (EXPLICIT_FORM) {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_continuing_points<E, true>(base_inputs[term.input], folding_challenge, gid, input0, input1);
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
      eval1 = E::add(eval1, E::mul(input1, term.challenge));
    }
  } else {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_continuing_points<E, false>(base_inputs[term.input], folding_challenge, gid, input0, input1);
      (void)input1;
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
    }
  }
}

template <typename E>
DEVICE_FORCEINLINE void
gkr_main_round0(const unsigned kind, const gkr_base_initial_source<bf> *base_inputs, const gkr_ext_initial_source<E> *ext_inputs,
                const gkr_base_initial_source<bf> *base_outputs, const gkr_ext_initial_source<E> *ext_outputs, const E *batch_challenges,
                const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];

  E c0 = E::ZERO();
  E c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    const E output_value = gkr_get_initial_base_value<E>(base_outputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    break;
  }
  case GKR_MAIN_PRODUCT: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    c1 = E::mul(batch_challenge_0, E::mul(delta_a, delta_b));
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    const E delta_mask = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_value = gkr_get_initial_delta(ext_inputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    c1 = E::mul(batch_challenge_0, E::mul(delta_mask, delta_value));
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    const E delta_c = gkr_get_initial_delta(ext_inputs[2], gid);
    const E delta_d = gkr_get_initial_delta(ext_inputs[3], gid);
    E num;
    E den;
    gkr_eval_lookup_pair(delta_a, delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_b = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_d = gkr_get_initial_base_delta<E>(base_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_base_pair_quadratic(delta_b, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_b = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_c = gkr_get_initial_base_delta<E>(base_inputs[1], gid);
    const E delta_d = gkr_get_initial_base_delta<E>(base_inputs[2], gid);
    E num;
    E den;
    gkr_eval_lookup_base_minus_multiplicity_quadratic(delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_d = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_unbalanced_quadratic(delta_d, delta_a, delta_b, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_a = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_c = gkr_get_initial_base_delta<E>(base_inputs[1], gid);
    const E delta_d = gkr_get_initial_delta(ext_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_cached_dens_and_setup_quadratic(delta_a, delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    c1 = E::mul(batch_challenge_0, gkr_eval_constraints_round0(base_inputs, gid, constraint_quadratic_terms, constraint_quadratic_terms_count));
    break;
  }
  default:
    return;
  }

  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round1(const unsigned kind, const gkr_base_after_one_source<bf, E> *base_inputs,
                                        const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges, const E *folding_challenge,
                                        const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                                        const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                                        const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions,
                                        const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];
  const E current_folding_challenge = folding_challenge[0];
  const E current_aux_challenge = aux_challenge[0];

  E c0 = E::ZERO();
  E c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_PRODUCT: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E eval0;
    E eval1;
    gkr_eval_product(a0, b0, eval0);
    gkr_eval_product(a1, b1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    E mask0;
    E mask1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, mask0, mask1);
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, value0, value1);
    E eval0;
    E eval1;
    gkr_eval_mask_identity(mask0, value0, eval0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_mask_identity(mask1, value1, eval1);
    } else {
      gkr_eval_mask_identity_quadratic(mask1, value1, eval1);
    }
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[3], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_pair(a0, b0, c0_in, d0, num0, den0);
    gkr_eval_lookup_pair(a1, b1, c1_in, d1, num1, den1);
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    E b0;
    E b1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    E b0;
    E b1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[2], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    E d0;
    E d1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    E a0;
    E a1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round1<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, constraint_quadratic_terms, constraint_quadratic_terms_count,
                                                  constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset[0], eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  default:
    return;
  }

  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round2(const unsigned kind, const gkr_base_after_two_source<bf, E> *base_inputs,
                                        const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges, const E *folding_challenges,
                                        const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                                        const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                                        const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions,
                                        const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];
  const E first_folding_challenge = folding_challenges[0];
  const E second_folding_challenge = folding_challenges[1];
  const E current_aux_challenge = aux_challenge[0];

  E c0 = E::ZERO();
  E c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_PRODUCT: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E eval0;
    E eval1;
    gkr_eval_product(a0, b0, eval0);
    gkr_eval_product(a1, b1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    E mask0;
    E mask1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, mask0, mask1);
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, value0, value1);
    E eval0;
    E eval1;
    gkr_eval_mask_identity(mask0, value0, eval0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_mask_identity(mask1, value1, eval1);
    } else {
      gkr_eval_mask_identity_quadratic(mask1, value1, eval1);
    }
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], second_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[3], second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_pair(a0, b0, c0_in, d0, num0, den0);
    gkr_eval_lookup_pair(a1, b1, c1_in, d1, num1, den1);
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    E b0;
    E b1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[1], first_folding_challenge, second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    E b0;
    E b1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[1], first_folding_challenge, second_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[2], first_folding_challenge, second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    E d0;
    E d1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    E a0;
    E a1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[1], first_folding_challenge, second_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round2<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, gid, constraint_quadratic_terms,
                                                  constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count,
                                                  constraint_constant_offset[0], eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  default:
    return;
  }

  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void
gkr_main_round3(const unsigned kind, const gkr_ext_continuing_source<E> *base_inputs, const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges,
                const E *folding_challenge, const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];
  const E current_folding_challenge = folding_challenge[0];
  const E current_aux_challenge = aux_challenge[0];

  E c0 = E::ZERO();
  E c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_PRODUCT: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E eval0;
    E eval1;
    gkr_eval_product(a0, b0, eval0);
    gkr_eval_product(a1, b1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    E mask0;
    E mask1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, mask0, mask1);
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, value0, value1);
    E eval0;
    E eval1;
    gkr_eval_mask_identity(mask0, value0, eval0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_mask_identity(mask1, value1, eval1);
    } else {
      gkr_eval_mask_identity_quadratic(mask1, value1, eval1);
    }
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[3], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_pair(a0, b0, c0_in, d0, num0, den0);
    gkr_eval_lookup_pair(a1, b1, c1_in, d1, num1, den1);
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[2], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round3<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, constraint_quadratic_terms, constraint_quadratic_terms_count,
                                                  constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset[0], eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  default:
    return;
  }

  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

#define GKR_DIM_REDUCING_KERNELS(arg_t)                                                                                                                        \
  EXTERN __global__ void ab_gkr_forward_layer_##arg_t##_kernel(const __grid_constant__ gkr_forward_layer_batch<arg_t> batch, const unsigned count) {           \
    gkr_forward_layer(batch, count);                                                                                                                           \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_forward_setup_generic_lookup_##arg_t##_kernel(const __grid_constant__ gkr_forward_setup_generic_lookup_batch<arg_t> batch,     \
                                                                              const unsigned row_count) {                                                      \
    gkr_forward_setup_generic_lookup(batch, row_count);                                                                                                        \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_forward_##arg_t##_kernel(const __grid_constant__ gkr_dim_reducing_forward_batch<arg_t> batch,                     \
                                                                      const unsigned row_count) {                                                              \
    gkr_dim_reducing_forward(batch, row_count);                                                                                                                \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_pairwise_round0_##arg_t##_kernel(const gkr_ext_initial_source<arg_t> *inputs,                                     \
                                                                              const gkr_ext_initial_source<arg_t> *outputs, const arg_t *batch_challenges,     \
                                                                              arg_t *contributions, const unsigned acc_size) {                                 \
    gkr_pairwise_round0(inputs, outputs, batch_challenges, contributions, acc_size);                                                                           \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_lookup_round0_##arg_t##_kernel(const gkr_ext_initial_source<arg_t> *inputs,                                       \
                                                                            const gkr_ext_initial_source<arg_t> *outputs, const arg_t *batch_challenges,       \
                                                                            arg_t *contributions, const unsigned acc_size) {                                   \
    gkr_lookup_round0(inputs, outputs, batch_challenges, contributions, acc_size);                                                                             \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_pairwise_continuation_##arg_t##_kernel(const gkr_ext_continuing_source<arg_t> *inputs,                            \
                                                                                    const arg_t *folding_challenge, const arg_t *batch_challenges,             \
                                                                                    const bool explicit_form, arg_t *contributions, const unsigned acc_size) { \
    if (explicit_form)                                                                                                                                         \
      gkr_pairwise_continuation<arg_t, true>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                            \
    else                                                                                                                                                       \
      gkr_pairwise_continuation<arg_t, false>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                           \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_lookup_continuation_##arg_t##_kernel(const gkr_ext_continuing_source<arg_t> *inputs,                              \
                                                                                  const arg_t *folding_challenge, const arg_t *batch_challenges,               \
                                                                                  const bool explicit_form, arg_t *contributions, const unsigned acc_size) {   \
    if (explicit_form)                                                                                                                                         \
      gkr_lookup_continuation<arg_t, true>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                              \
    else                                                                                                                                                       \
      gkr_lookup_continuation<arg_t, false>(inputs, folding_challenge, batch_challenges, contributions, acc_size);                                             \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_dim_reducing_build_eq_##arg_t##_kernel(const arg_t *claim_point, const unsigned challenge_offset,                              \
                                                                       const unsigned challenge_count, arg_t *eq_values, const unsigned acc_size) {            \
    gkr_build_eq_values(claim_point, challenge_offset, challenge_count, eq_values, acc_size);                                                                  \
  }

GKR_DIM_REDUCING_KERNELS(e2);
GKR_DIM_REDUCING_KERNELS(e4);
GKR_DIM_REDUCING_KERNELS(e6);

#define GKR_MAIN_LAYER_KERNELS(arg_t)                                                                                                                          \
  EXTERN __global__ void ab_gkr_main_round0_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_base_initial_source<bf> *base_inputs, const gkr_ext_initial_source<arg_t> *ext_inputs,                                    \
      const gkr_base_initial_source<bf> *base_outputs, const gkr_ext_initial_source<arg_t> *ext_outputs, const arg_t *batch_challenges,                        \
      const arg_t *aux_challenge, const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms,                                                 \
      const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms,                                  \
      const unsigned constraint_linear_terms_count, const arg_t *constraint_constant_offset, arg_t *contributions, const unsigned acc_size) {                  \
    gkr_main_round0(kind, base_inputs, ext_inputs, base_outputs, ext_outputs, batch_challenges, aux_challenge, constraint_quadratic_terms,                     \
                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset, contributions,       \
                    acc_size);                                                                                                                                 \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round1_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_base_after_one_source<bf, arg_t> *base_inputs, const gkr_ext_continuing_source<arg_t> *ext_inputs,                        \
      const arg_t *batch_challenges, const arg_t *folding_challenge, const arg_t *aux_challenge,                                                               \
      const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms, const unsigned constraint_quadratic_terms_count,                            \
      const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms, const unsigned constraint_linear_terms_count,                                     \
      const arg_t *constraint_constant_offset, const bool explicit_form, arg_t *contributions, const unsigned acc_size) {                                      \
    if (explicit_form)                                                                                                                                         \
      gkr_main_round1<arg_t, true>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,              \
                                   constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,       \
                                   contributions, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round1<arg_t, false>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,             \
                                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,      \
                                    contributions, acc_size);                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round2_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_base_after_two_source<bf, arg_t> *base_inputs, const gkr_ext_continuing_source<arg_t> *ext_inputs,                        \
      const arg_t *batch_challenges, const arg_t *folding_challenges, const arg_t *aux_challenge,                                                              \
      const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms, const unsigned constraint_quadratic_terms_count,                            \
      const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms, const unsigned constraint_linear_terms_count,                                     \
      const arg_t *constraint_constant_offset, const bool explicit_form, arg_t *contributions, const unsigned acc_size) {                                      \
    if (explicit_form)                                                                                                                                         \
      gkr_main_round2<arg_t, true>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenges, aux_challenge, constraint_quadratic_terms,             \
                                   constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,       \
                                   contributions, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round2<arg_t, false>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenges, aux_challenge, constraint_quadratic_terms,            \
                                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,      \
                                    contributions, acc_size);                                                                                                  \
  }                                                                                                                                                            \
  EXTERN __global__ void ab_gkr_main_round3_##arg_t##_kernel(                                                                                                  \
      const unsigned kind, const gkr_ext_continuing_source<arg_t> *base_inputs, const gkr_ext_continuing_source<arg_t> *ext_inputs,                            \
      const arg_t *batch_challenges, const arg_t *folding_challenge, const arg_t *aux_challenge,                                                               \
      const gkr_main_constraint_quadratic_term<arg_t> *constraint_quadratic_terms, const unsigned constraint_quadratic_terms_count,                            \
      const gkr_main_constraint_linear_term<arg_t> *constraint_linear_terms, const unsigned constraint_linear_terms_count,                                     \
      const arg_t *constraint_constant_offset, const bool explicit_form, arg_t *contributions, const unsigned acc_size) {                                      \
    if (explicit_form)                                                                                                                                         \
      gkr_main_round3<arg_t, true>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,              \
                                   constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,       \
                                   contributions, acc_size);                                                                                                   \
    else                                                                                                                                                       \
      gkr_main_round3<arg_t, false>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge, constraint_quadratic_terms,             \
                                    constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset,      \
                                    contributions, acc_size);                                                                                                  \
  }

GKR_MAIN_LAYER_KERNELS(e2);
GKR_MAIN_LAYER_KERNELS(e4);
GKR_MAIN_LAYER_KERNELS(e6);

#define GKR_FORWARD_CACHE_KERNELS(arg_t)                                                                                                                       \
  EXTERN __global__ void ab_gkr_forward_cache_##arg_t##_kernel(const __grid_constant__ gkr_forward_cache_batch<arg_t> batch, const unsigned trace_len) {       \
    gkr_forward_cache(batch, trace_len);                                                                                                                       \
  }

GKR_FORWARD_CACHE_KERNELS(e2);
GKR_FORWARD_CACHE_KERNELS(e4);
GKR_FORWARD_CACHE_KERNELS(e6);

} // namespace airbender::ops::complex
