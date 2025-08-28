#include "common.cuh"
#include "field.cuh"

using namespace ::airbender::field;

namespace airbender::blake2s {

typedef uint32_t u32;
typedef uint64_t u64;
typedef base_field bf;

#define ROTR32(x, y) (((x) >> (y)) ^ ((x) << (32 - (y))))

#define G(a, b, c, d, x, y)                                                                                                                                    \
  v[a] = v[a] + v[b] + (x);                                                                                                                                    \
  v[d] = ROTR32(v[d] ^ v[a], 16);                                                                                                                              \
  v[c] = v[c] + v[d];                                                                                                                                          \
  v[b] = ROTR32(v[b] ^ v[c], 12);                                                                                                                              \
  v[a] = v[a] + v[b] + (y);                                                                                                                                    \
  v[d] = ROTR32(v[d] ^ v[a], 8);                                                                                                                               \
  v[c] = v[c] + v[d];                                                                                                                                          \
  v[b] = ROTR32(v[b] ^ v[c], 7);

constexpr bool USE_REDUCED_ROUNDS = true;
constexpr unsigned FULL_ROUNDS = 10;
constexpr unsigned REDUCED_ROUNDS = 7;
constexpr unsigned ROUNDS = USE_REDUCED_ROUNDS ? REDUCED_ROUNDS : FULL_ROUNDS;
constexpr unsigned STATE_SIZE = 8;
constexpr unsigned BLOCK_SIZE = 16;
constexpr u32 IV_0_TWIST = 0x01010000 ^ 32;
#define IV_DEF constexpr u32 IV[STATE_SIZE] = {0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19}
#define SIGMAS_DEF                                                                                                                                             \
  constexpr unsigned SIGMAS[10][BLOCK_SIZE] = {{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3}, \
                                               {11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4}, {7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8}, \
                                               {9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13}, {2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9}, \
                                               {12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11}, {13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10}, \
                                               {6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5}, {10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0}}

DEVICE_FORCEINLINE void initialize(u32 state[STATE_SIZE]) {
  IV_DEF;
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    state[i] = IV[i];
  state[0] ^= IV_0_TWIST;
}

template <bool IS_FINAL_BLOCK> DEVICE_FORCEINLINE void compress(u32 state[STATE_SIZE], u32 &t, const u32 m[BLOCK_SIZE], const unsigned block_size) {
  IV_DEF;
  SIGMAS_DEF;
  u32 v[BLOCK_SIZE];
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++) {
    v[i] = state[i];
    v[i + STATE_SIZE] = IV[i];
  }
  t += (IS_FINAL_BLOCK ? block_size : BLOCK_SIZE) * sizeof(u32);
  v[12] ^= t;
  if (IS_FINAL_BLOCK)
    v[14] ^= 0xffffffff;
#pragma unroll
  for (unsigned i = 0; i < ROUNDS; i++) {
    const auto s = SIGMAS[i];
    G(0, 4, 8, 12, m[s[0]], m[s[1]])
    G(1, 5, 9, 13, m[s[2]], m[s[3]])
    G(2, 6, 10, 14, m[s[4]], m[s[5]])
    G(3, 7, 11, 15, m[s[6]], m[s[7]])
    G(0, 5, 10, 15, m[s[8]], m[s[9]])
    G(1, 6, 11, 12, m[s[10]], m[s[11]])
    G(2, 7, 8, 13, m[s[12]], m[s[13]])
    G(3, 4, 9, 14, m[s[14]], m[s[15]])
  }
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; ++i)
    state[i] ^= v[i] ^ v[i + STATE_SIZE];
}

EXTERN __global__ void ab_blake2s_leaves_kernel(const bf *values, u32 *results, const unsigned log_rows_count, const unsigned cols_count,
                                                const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  values += gid << log_rows_count;
  results += gid * STATE_SIZE;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  auto read = [=](const unsigned offset) {
    const unsigned row = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    return col < cols_count ? bf::into_canonical_u32(load_cs(values + row + (col * count << log_rows_count))) : 0;
  };
  u32 state[STATE_SIZE];
  u32 block[BLOCK_SIZE];
  initialize(state);
  u32 t = 0;
  const unsigned values_count = cols_count << log_rows_count;
  unsigned offset = 0;
  while (offset < values_count) {
    const unsigned remaining = values_count - offset;
    const bool is_final_block = remaining <= BLOCK_SIZE;
#pragma unroll
    for (unsigned i = 0; i < BLOCK_SIZE; i++, offset++)
      block[i] = read(offset);
    if (is_final_block)
      compress<true>(state, t, block, remaining);
    else
      compress<false>(state, t, block, BLOCK_SIZE);
  }
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    store_cs(&results[i], state[i]);
}

EXTERN __global__ void ab_blake2s_nodes_kernel(const u32 *values, u32 *results, const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  values += gid * BLOCK_SIZE;
  results += gid * STATE_SIZE;
  u32 state[STATE_SIZE];
  u32 block[BLOCK_SIZE];
  initialize(state);
  u32 t = 0;
#pragma unroll
  for (unsigned i = 0; i < BLOCK_SIZE; i++, values++)
    block[i] = load_cs(values);
  compress<true>(state, t, block, BLOCK_SIZE);
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    store_cs(&results[i], state[i]);
}

EXTERN __global__ void ab_gather_rows_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                             const unsigned log_rows_count, const matrix_getter<bf, ld_modifier::cs> values,
                                             const matrix_setter<bf, st_modifier::cs> results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned i = indexes[idx];
  const unsigned index = bit_reverse_indexes ? __brev(i) >> (32 - log_rows_count) : i;
  const unsigned src_row = index * blockDim.x + threadIdx.x;
  const unsigned dst_row = idx * blockDim.x + threadIdx.x;
  const unsigned col = blockIdx.y;
  const bf value = values.get(src_row, col);
  const bf result(bf::into_canonical_u32(value));
  results.set(dst_row, col, result);
}

EXTERN __global__ void ab_gather_merkle_paths_kernel(const unsigned *indexes, const unsigned indexes_count, const u32 *values, const unsigned log_leaves_count,
                                                     u32 *results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned leaf_index = indexes[idx];
  const unsigned layer_index = blockIdx.y;
  const unsigned layer_offset = ((1u << log_leaves_count + 1) - (1u << log_leaves_count + 1 - layer_index)) * STATE_SIZE;
  const unsigned hash_offset = (leaf_index >> layer_index ^ 1) * STATE_SIZE;
  const unsigned element_offset = threadIdx.x;
  const unsigned src_index = layer_offset + hash_offset + element_offset;
  const unsigned dst_index = layer_index * indexes_count * STATE_SIZE + idx * STATE_SIZE + element_offset;
  results[dst_index] = values[src_index];
}

EXTERN __global__ void ab_blake2s_pow_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  const uint32_t digest_mask = 0xffffffff << 32 - bits_count;
  __align__(8) u32 m_u32[BLOCK_SIZE] = {};
  auto m_u64 = reinterpret_cast<u64 *>(m_u32);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    m_u64[i] = seed[i];
  const unsigned stride = blockDim.x * gridDim.x;
  for (uint64_t nonce = threadIdx.x + blockIdx.x * blockDim.x; nonce < max_nonce; nonce += stride) {
    m_u64[STATE_SIZE / 2] = nonce;
    u32 state[STATE_SIZE];
    initialize(state);
    u32 t = 0;
    compress<true>(state, t, m_u32, STATE_SIZE + 2);
    if (!(state[0] & digest_mask)) {
      atomicCAS(reinterpret_cast<unsigned long long *>(const_cast<u64 *>(result)), UINT64_MAX, nonce);
      __threadfence();
    }
    if (*result != UINT64_MAX)
      return;
  }
}

} // namespace airbender::blake2s