#include "../primitives/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::ops::blake2s {

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

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) {
  return num_bits == 0 ? 0 : (__brev(value) >> (32 - num_bits));
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
  results += gid * STATE_SIZE;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  const unsigned domain_size = count << log_rows_count;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    const unsigned row = gid + bitreverse_low_bits(row_slot, log_rows_count) * count;
    return col < cols_count ? bf::into_raw_u32(load_cs(values + row + col * domain_size)) : 0;
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
  const bf result = values.get(src_row, col);
  results.set(dst_row, col, result);
}

EXTERN __global__ void ab_gather_leaf_rows_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                                  const unsigned log_leaves_count, const unsigned log_rows_per_leaf,
                                                  const matrix_getter<bf, ld_modifier::cs> values, const matrix_setter<bf, st_modifier::cs> results) {
  const unsigned idx = threadIdx.y + blockIdx.x * blockDim.y;
  if (idx >= indexes_count)
    return;
  const unsigned i = indexes[idx];
  const unsigned leaf_index = bit_reverse_indexes ? __brev(i) >> (32 - log_leaves_count) : i;
  const unsigned leaves_count = 1u << log_leaves_count;
  const unsigned src_row = leaf_index + bitreverse_low_bits(threadIdx.x, log_rows_per_leaf) * leaves_count;
  const unsigned dst_row = (idx << log_rows_per_leaf) + threadIdx.x;
  const unsigned col = blockIdx.y;
  const bf result = values.get(src_row, col);
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

constexpr unsigned WARP_SIZE = 32;
constexpr unsigned LOG_WARP_SIZE = 5;
constexpr unsigned WARP_MASK = WARP_SIZE - 1;
constexpr u32 FULL_MASK = 0xffffffff;

EXTERN __global__ void ab_gather_rows_and_merkle_paths_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                                              const bf *values, const unsigned log_rows_per_leaf, const unsigned cols_count,
                                                              const unsigned log_total_leaves_count, const matrix_setter<bf, st_modifier::cs> leaf_values,
                                                              const u32 *tree_bottom, const unsigned layers_count, u32 *merkle_paths) {
  // This fused kernel is for partial-tree queries: it hashes the queried leaves, writes the first
  // LOG_WARP_SIZE sibling layers from warp-local reductions, then resumes path collection from
  // the cached upper tree pointed to by tree_bottom.
  const unsigned lane_idx = threadIdx.x;
  const unsigned idx = blockIdx.x;
  if (idx >= indexes_count)
    return;
  const unsigned query_index = indexes[idx];
  const unsigned index_lane = (query_index & ~WARP_MASK) | lane_idx;
  const bool is_output_lane = query_index == index_lane;
  const unsigned leaf_index = bit_reverse_indexes ? __brev(index_lane) >> (32 - log_total_leaves_count) : index_lane;
  const unsigned log_rows_count = log_total_leaves_count + log_rows_per_leaf;
  const unsigned leaves_count = 1u << log_total_leaves_count;
  merkle_paths += idx * STATE_SIZE;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & ((1u << log_rows_per_leaf) - 1);
    const unsigned col = offset >> log_rows_per_leaf;
    const unsigned row = leaf_index + bitreverse_low_bits(row_slot, log_rows_per_leaf) * leaves_count;
    const auto address = values + row + (col << log_rows_count);
    return col < cols_count ? bf::into_raw_u32(load_cs(address)) : 0;
  };
  u32 state[STATE_SIZE];
  u32 block[BLOCK_SIZE];
  initialize(state);
  u32 t = 0;
  const unsigned values_count = cols_count << log_rows_per_leaf;
  unsigned offset = 0;
  while (offset < values_count) {
    const unsigned remaining = values_count - offset;
    const bool is_final_block = remaining <= BLOCK_SIZE;
#pragma unroll
    for (unsigned i = 0; i < BLOCK_SIZE; i++, offset++) {
      const u32 value = read(offset);
      block[i] = value;
      if (is_output_lane && offset < values_count) {
        const unsigned row = offset & ((1u << log_rows_per_leaf) - 1);
        const unsigned col = offset >> log_rows_per_leaf;
        leaf_values.set((idx << log_rows_per_leaf) + row, col, bf::from_raw_u32(value));
      }
    }
    if (is_final_block)
      compress<true>(state, t, block, remaining);
    else
      compress<false>(state, t, block, BLOCK_SIZE);
  }
#pragma unroll
  for (unsigned layer = 0; layer < LOG_WARP_SIZE; layer++) {
    u32 other_state[STATE_SIZE];
    const bool take_other_first = (lane_idx >> layer) & 1;
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++) {
      other_state[i] = __shfl_xor_sync(FULL_MASK, state[i], 1 << layer);
      if (is_output_lane)
        merkle_paths[i] = other_state[i];
      if (take_other_first) {
        block[i] = other_state[i];
        block[i + STATE_SIZE] = state[i];
      } else {
        block[i] = state[i];
        block[i + STATE_SIZE] = other_state[i];
      }
    }
    initialize(state);
    t = 0;
    compress<true>(state, t, block, BLOCK_SIZE);
    merkle_paths += indexes_count * STATE_SIZE;
  }
  if (lane_idx >= STATE_SIZE)
    return;
  unsigned digest_index = query_index >> LOG_WARP_SIZE;
  unsigned log_digests_count = log_total_leaves_count - LOG_WARP_SIZE;
  const u32 *tree_layer = tree_bottom + lane_idx;
  u32 *merkle_paths_dst = merkle_paths + lane_idx;
  for (unsigned layer = LOG_WARP_SIZE; layer < layers_count; layer++) {
    const unsigned other_index = digest_index ^ 1;
    *merkle_paths_dst = *(tree_layer + other_index * STATE_SIZE);
    digest_index >>= 1;
    tree_layer += (1u << log_digests_count) * STATE_SIZE;
    log_digests_count--;
    merkle_paths_dst += indexes_count * STATE_SIZE;
  }
}

EXTERN __global__ void ab_gather_merkle_paths_from_rows_kernel(const unsigned *indexes, const unsigned indexes_count, const bool bit_reverse_indexes,
                                                               const bf *values, const unsigned log_rows_per_leaf, const unsigned cols_count,
                                                               const unsigned log_total_leaves_count, const u32 *tree_bottom, const unsigned layers_count,
                                                               u32 *merkle_paths) {
  const unsigned lane_idx = threadIdx.x;
  const unsigned idx = blockIdx.x;
  if (idx >= indexes_count)
    return;
  const unsigned query_index = indexes[idx];
  const unsigned index_lane = (query_index & ~WARP_MASK) | lane_idx;
  const bool is_output_lane = query_index == index_lane;
  const unsigned leaf_index = bit_reverse_indexes ? __brev(index_lane) >> (32 - log_total_leaves_count) : index_lane;
  const unsigned log_rows_count = log_total_leaves_count + log_rows_per_leaf;
  const unsigned leaves_count = 1u << log_total_leaves_count;
  merkle_paths += idx * STATE_SIZE;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & ((1u << log_rows_per_leaf) - 1);
    const unsigned col = offset >> log_rows_per_leaf;
    const unsigned row = leaf_index + bitreverse_low_bits(row_slot, log_rows_per_leaf) * leaves_count;
    const auto address = values + row + (col << log_rows_count);
    return col < cols_count ? bf::into_raw_u32(load_cs(address)) : 0;
  };
  u32 state[STATE_SIZE];
  u32 block[BLOCK_SIZE];
  initialize(state);
  u32 t = 0;
  const unsigned values_count = cols_count << log_rows_per_leaf;
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
  for (unsigned layer = 0; layer < LOG_WARP_SIZE; layer++) {
    u32 other_state[STATE_SIZE];
    const bool take_other_first = (lane_idx >> layer) & 1;
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++) {
      other_state[i] = __shfl_xor_sync(FULL_MASK, state[i], 1 << layer);
      if (is_output_lane)
        merkle_paths[i] = other_state[i];
      if (take_other_first) {
        block[i] = other_state[i];
        block[i + STATE_SIZE] = state[i];
      } else {
        block[i] = state[i];
        block[i + STATE_SIZE] = other_state[i];
      }
    }
    initialize(state);
    t = 0;
    compress<true>(state, t, block, BLOCK_SIZE);
    merkle_paths += indexes_count * STATE_SIZE;
  }
  if (lane_idx >= STATE_SIZE)
    return;
  unsigned digest_index = query_index >> LOG_WARP_SIZE;
  unsigned log_digests_count = log_total_leaves_count - LOG_WARP_SIZE;
  const u32 *tree_layer = tree_bottom + lane_idx;
  u32 *merkle_paths_dst = merkle_paths + lane_idx;
  for (unsigned layer = LOG_WARP_SIZE; layer < layers_count; layer++) {
    const unsigned other_index = digest_index ^ 1;
    *merkle_paths_dst = *(tree_layer + other_index * STATE_SIZE);
    digest_index >>= 1;
    tree_layer += (1u << log_digests_count) * STATE_SIZE;
    log_digests_count--;
    merkle_paths_dst += indexes_count * STATE_SIZE;
  }
}

EXTERN __global__ void ab_blake2s_pow_kernel(const u64 *seed, const u32 bits_count, const u64 max_nonce, volatile u64 *result) {
  const u32 digest_mask = 0xffffffff << 32 - bits_count;
  const auto result_ptr = reinterpret_cast<unsigned long long *>(const_cast<u64 *>(result));
  __align__(8) u32 m_u32[BLOCK_SIZE] = {};
  auto m_u64 = reinterpret_cast<u64 *>(m_u32);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    m_u64[i] = seed[i];
  const unsigned stride = blockDim.x * gridDim.x;
  for (u64 nonce = threadIdx.x + blockIdx.x * blockDim.x; nonce < max_nonce; nonce += stride) {
    m_u64[STATE_SIZE / 2] = nonce;
    u32 state[STATE_SIZE];
    initialize(state);
    u32 t = 0;
    compress<true>(state, t, m_u32, STATE_SIZE + 2);
    if (!(state[0] & digest_mask)) {
#ifdef AB_DETERMINISTIC_POW
      atomicMin(result_ptr, static_cast<unsigned long long>(nonce));
#else
      atomicCAS(result_ptr, UINT64_MAX, nonce);
#endif
      __threadfence();
    }
    if (*result
#ifdef AB_DETERMINISTIC_POW
        <= nonce
#else
        != UINT64_MAX
#endif
    )
      return;
  }
}

// ---------------------------------------------------------------------------
// Device-side Fiat-Shamir transcript operations (single-thread kernels).
// These mirror the host Blake2sTranscript::commit_with_seed / draw_randomness
// so that challenge derivation can happen entirely on the device without D2H
// round-trips.
// ---------------------------------------------------------------------------

// commit_with_seed: new_seed = Blake2s(old_seed || input).
// seed_io: STATE_SIZE u32 words, read then overwritten with the new seed.
// input:   input_len u32 words to absorb after the seed.
EXTERN __global__ void ab_transcript_commit_kernel(u32 *seed_io, const u32 *input, const unsigned input_len) {
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];

  // Start the block with the seed.
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = seed_io[i];
#pragma unroll
  for (unsigned i = STATE_SIZE; i < BLOCK_SIZE; i++)
    block[i] = 0;

  unsigned block_offset = STATE_SIZE;
  unsigned remaining = input_len;
  const u32 *src = input;

  while (remaining > 0) {
    const unsigned space = BLOCK_SIZE - block_offset;
    const unsigned n = remaining < space ? remaining : space;
    for (unsigned i = 0; i < n; i++)
      block[block_offset + i] = src[i];
    block_offset += n;
    src += n;
    remaining -= n;

    if (block_offset == BLOCK_SIZE && remaining > 0) {
      compress<false>(state, t, block, BLOCK_SIZE);
#pragma unroll
      for (unsigned i = 0; i < BLOCK_SIZE; i++)
        block[i] = 0;
      block_offset = 0;
    }
  }

  // Zero-pad and finalize.
  for (unsigned i = block_offset; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, block_offset);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_io[i] = state[i];
}

// draw_randomness: expand seed into output_len u32 words.
// The first STATE_SIZE words are the seed itself (no hashing).
// Each subsequent STATE_SIZE-word chunk hashes the seed to advance it.
// seed_io:    STATE_SIZE u32 words; updated in-place when output_len > STATE_SIZE.
// output:     output_len u32 words (must be a multiple of STATE_SIZE).
// output_len: total words to produce.
EXTERN __global__ void ab_transcript_squeeze_kernel(u32 *seed_io, u32 *output, const unsigned output_len) {
  // Round 0: emit the current seed verbatim.
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    output[i] = seed_io[i];

  const unsigned num_rounds = output_len / STATE_SIZE;
  for (unsigned round = 1; round < num_rounds; round++) {
    u32 state[STATE_SIZE];
    initialize(state);
    u32 block[BLOCK_SIZE] = {};
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++)
      block[i] = seed_io[i];
    u32 t = 0;
    compress<true>(state, t, block, STATE_SIZE);

#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++) {
      seed_io[i] = state[i];
      output[round * STATE_SIZE + i] = state[i];
    }
  }
}

// Device-side `Transcript::commit_initial` seed → `draw_random_field_els::<BF, E4>(seed, count)`.
// Writes `count` E4 challenges in Montgomery form, matching host
// `BabyBearField::from_raw_repr_with_reduction` applied to each 4-u32 squeeze chunk, and
// updates `seed_io` with the advanced seed.
//
// `count` must be positive. Each challenge consumes 4 consecutive raw squeeze u32 words; the
// kernel advances the seed once per STATE_SIZE (= 8) raw words produced (i.e. every 2 E4s),
// matching the CPU's `draw_randomness` chunking with `next_multiple_of(STATE_SIZE)` padding.
EXTERN __global__ void ab_transcript_squeeze_e4_kernel(u32 *seed_io, e4 *output_e4, const unsigned count) {
  if (count == 0)
    return;
  // Produce enough raw u32 words for `count` E4 challenges, padded to a multiple of STATE_SIZE.
  const unsigned raw_len = ((count * 4u + STATE_SIZE - 1u) / STATE_SIZE) * STATE_SIZE;
  const unsigned num_rounds = raw_len / STATE_SIZE;

  u32 raw_chunk[STATE_SIZE];
  // Round 0: verbatim seed.
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    raw_chunk[i] = seed_io[i];

  unsigned emitted = 0;
  for (unsigned round = 0; round < num_rounds; round++) {
    if (round > 0) {
      // Advance seed by Blake2s(seed) and refill raw_chunk.
      u32 state[STATE_SIZE];
      initialize(state);
      u32 block[BLOCK_SIZE] = {};
#pragma unroll
      for (unsigned i = 0; i < STATE_SIZE; i++)
        block[i] = seed_io[i];
      u32 t = 0;
      compress<true>(state, t, block, STATE_SIZE);
#pragma unroll
      for (unsigned i = 0; i < STATE_SIZE; i++) {
        seed_io[i] = state[i];
        raw_chunk[i] = state[i];
      }
    }
    // Consume raw_chunk 4 u32s at a time → 1 E4 challenge.
    for (unsigned slot = 0; slot < STATE_SIZE / 4 && emitted < count; slot++) {
      const u32 *src = &raw_chunk[slot * 4];
      const bf c0 = bf::from_raw_repr_with_reduction(src[0]);
      const bf c1 = bf::from_raw_repr_with_reduction(src[1]);
      const bf c2 = bf::from_raw_repr_with_reduction(src[2]);
      const bf c3 = bf::from_raw_repr_with_reduction(src[3]);
      const e4 ch = e4(e2(c0, c1), e2(c2, c3));
      output_e4[emitted] = ch;
      emitted++;
    }
  }
}

// ---------------------------------------------------------------------------
// Backward sumcheck per-round state update (device-side).
//
// Replaces the host callback that runs after each CUB reduction. Consumes the
// reduction outputs (c_partial, e_partial), the previous-round claim point
// coordinate, and the running (seed, claim, eq_prefactor) state, then:
//   1. normalizes the claim by inverting the eq prefactor,
//   2. derives the round's 4 univariate coefficients [c0..c3],
//   3. commits those coefficients to the transcript (Blake2s),
//   4. extracts the new folding challenge from the first 4 u32 words of the
//      updated seed (matching host `BabyBearField::from_raw_repr_with_reduction`),
//   5. folds the claim through the univariate poly at the challenge,
//   6. refreshes eq_prefactor = eq(challenge, prev_coord).
//
// All I/O buffers are on device. The kernel is launched <<<1,1>>>. Memory
// layout of e4 is 4 consecutive u32 words (Montgomery-form base field limbs),
// matching the host flatten order for commit_field_els.
// ---------------------------------------------------------------------------

DEVICE_FORCEINLINE e4 e4_from_raw_u32x4(const u32 *words) {
  return e4(e2(bf::from_raw_repr_with_reduction(words[0]), bf::from_raw_repr_with_reduction(words[1])),
            e2(bf::from_raw_repr_with_reduction(words[2]), bf::from_raw_repr_with_reduction(words[3])));
}

// Port of prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic.
DEVICE_FORCEINLINE void compute_univariate_coeffs_max_quadratic(const e4 prev_challenge, const e4 prev_claim, const e4 e, const e4 c, e4 out[4]) {
  const e4 ONE = e4::ONE();
  const e4 b = e4::sub(ONE, prev_challenge);
  const e4 a = e4::sub(e4::dbl(prev_challenge), ONE);
  // a + b = prev_challenge.
  const e4 a_plus_b_inv = e4::inv(prev_challenge);

  const e4 be = e4::mul(b, e);
  e4 d = e4::sub(prev_claim, be);
  d = e4::mul(d, a_plus_b_inv);
  d = e4::sub(d, c);
  d = e4::sub(d, e);

  out[0] = be;
  out[1] = e4::add(e4::mul(a, e), e4::mul(b, d));
  out[2] = e4::add(e4::mul(a, d), e4::mul(b, c));
  out[3] = e4::mul(a, c);
}

// Horner evaluation of a degree-3 polynomial with 4 coefficients.
DEVICE_FORCEINLINE e4 eval_degree3_poly(const e4 coeffs[4], const e4 point) {
  e4 r = coeffs[3];
  r = e4::add(e4::mul(r, point), coeffs[2]);
  r = e4::add(e4::mul(r, point), coeffs[1]);
  r = e4::add(e4::mul(r, point), coeffs[0]);
  return r;
}

// eq(x, y) = x*y + (1-x)*(1-y).
DEVICE_FORCEINLINE e4 eq_poly(const e4 x, const e4 y) {
  const e4 ONE = e4::ONE();
  const e4 t = e4::mul(e4::sub(ONE, x), e4::sub(ONE, y));
  return e4::add(e4::mul(x, y), t);
}

EXTERN __global__ void ab_backward_sumcheck_round_update_kernel(const e4 *reduction_output, const e4 *prev_claim_coord, u32 *seed_io, e4 *claim_io,
                                                                e4 *eq_prefactor_io, e4 *coeffs_out, e4 *challenge_out) {
  // Load state.
  const e4 e_partial = reduction_output[0];
  const e4 c_partial = reduction_output[1];
  const e4 prev_coord = *prev_claim_coord;
  const e4 claim = *claim_io;
  const e4 eq_prefactor = *eq_prefactor_io;

  // Normalize the running claim by the accumulated eq prefactor.
  const e4 normalized_claim = e4::mul(claim, e4::inv(eq_prefactor));

  // Derive the round's 4 univariate coefficients.
  e4 coeffs[4];
  compute_univariate_coeffs_max_quadratic(prev_coord, normalized_claim, e_partial, c_partial, coeffs);
#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    coeffs_out[i] = coeffs[i];

  // Blake2s commit: seed (8 words) || flatten(coeffs) (16 words) = 24 words,
  // processed as one non-final 16-word block followed by one final 8-word
  // block. e4 layout is 4 contiguous u32 limbs per element, already Montgomery,
  // matching the host's as_u32_raw_repr_reduced flatten order.
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = seed_io[i];
  const u32 *coeff_words = reinterpret_cast<const u32 *>(&coeffs[0]);
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[STATE_SIZE + i] = coeff_words[i];
  compress<false>(state, t, block, BLOCK_SIZE);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = coeff_words[STATE_SIZE + i];
#pragma unroll
  for (unsigned i = STATE_SIZE; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, STATE_SIZE);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_io[i] = state[i];

  // Derive the folding challenge from the first 4 words of the new seed.
  // draw_random_field_els<E4>(seed, 1) produces 8 padding words but consumes
  // only 4 — the seed itself is not further hashed for a single draw.
  const e4 challenge = e4_from_raw_u32x4(state);
  *challenge_out = challenge;

  // Fold the claim and refresh the eq prefactor.
  *claim_io = eval_degree3_poly(coeffs, challenge);
  *eq_prefactor_io = eq_poly(challenge, prev_coord);
}

// ---------------------------------------------------------------------------
// WHIR fold per-round state update (device-side).
//
// Replaces the host callback that runs after each special 3-point evaluation.
// Consumes the three reduction outputs (f(0), f(1), raw ⟨eval_l+eval_h,
// eq_l+eq_h⟩) and the running transcript seed, then:
//   1. computes f(1/2) = reduction_output[2] * (1/4),
//   2. Lagrange-interpolates the degree-2 sumcheck univariate at (0, 1, 1/2),
//   3. commits those 3 E4 coefficients to the transcript (Blake2s),
//   4. extracts the fold challenge from the first 4 u32 words of the updated
//      seed (matching host `BabyBearField::from_raw_repr_with_reduction`).
//
// All I/O buffers are on device. The kernel is launched <<<1,1>>>. Memory
// layout of e4 is 4 consecutive u32 limbs (Montgomery-form base field), which
// matches the host flatten order used by commit_field_els.
// ---------------------------------------------------------------------------
EXTERN __global__ void ab_whir_fold_round_update_kernel(const e4 *reduction_output, u32 *seed_io, e4 *coeffs_out, e4 *challenge_out) {
  // Derive constants: quart = 1/4, two_inv = 1/2 (Montgomery form).
  const bf two = bf::from_canonical_u32(2);
  const bf four = bf::from_canonical_u32(4);
  const bf two_inv_bf = bf::inv(two);
  const bf quart_bf = bf::inv(four);
  const e4 random_point = e4::from_scalar(two_inv_bf);
  const e4 ONE = e4::ONE();
  const e4 ZERO = e4::ZERO();

  // Load evals and scale the half-point evaluation by 1/4 (the host does
  // `values[2].mul_assign_by_base(&quart)`).
  const e4 eval_at_0 = reduction_output[0];
  const e4 eval_at_1 = reduction_output[1];
  const e4 eval_at_random = e4::mul(reduction_output[2], quart_bf);

  // Lagrange interpolant at x in {0, 1, random_point = 1/2}.
  //   coeffs_for_0      = [rp, -(1+rp), 1]
  //   coeffs_for_1      = [ 0,     -rp, 1]
  //   coeffs_for_random = [ 0,      -1, 1]
  e4 coeffs_for_0[3];
  coeffs_for_0[0] = random_point;
  coeffs_for_0[1] = e4::neg(e4::add(ONE, random_point));
  coeffs_for_0[2] = ONE;

  e4 coeffs_for_1[3];
  coeffs_for_1[0] = ZERO;
  coeffs_for_1[1] = e4::neg(random_point);
  coeffs_for_1[2] = ONE;

  e4 coeffs_for_random[3];
  coeffs_for_random[0] = ZERO;
  coeffs_for_random[1] = e4::neg(ONE);
  coeffs_for_random[2] = ONE;

  // Denominators:
  //   dens[0] = (0 - 1) * (0 - rp) = rp
  //   dens[1] = (1 - rp)
  //   dens[2] = rp * (rp - 1)
  e4 dens[3];
  dens[0] = random_point;
  dens[1] = e4::sub(ONE, random_point);
  dens[2] = e4::mul(random_point, e4::sub(random_point, ONE));

  // Three inversions (launched <<<1,1>>> — no parallelism to gain from a
  // batched Montgomery trick here, and explicit inv keeps the bookkeeping
  // obvious).
  dens[0] = e4::inv(dens[0]);
  dens[1] = e4::inv(dens[1]);
  dens[2] = e4::inv(dens[2]);

  // Accumulate interpolant coefficients.
  const e4 evals[3] = {eval_at_0, eval_at_1, eval_at_random};
  const e4 *coeff_tables[3] = {coeffs_for_0, coeffs_for_1, coeffs_for_random};
  e4 result[3] = {ZERO, ZERO, ZERO};
#pragma unroll
  for (unsigned j = 0; j < 3; j++) {
    const e4 eval_den = e4::mul(evals[j], dens[j]);
#pragma unroll
    for (unsigned i = 0; i < 3; i++) {
      result[i] = e4::add(result[i], e4::mul(eval_den, coeff_tables[j][i]));
    }
  }

#pragma unroll
  for (unsigned i = 0; i < 3; i++)
    coeffs_out[i] = result[i];

  // Blake2s commit: seed (8 words) || flatten(3 × E4 = 12 words) = 20 words.
  // One non-final 16-word block, then one final 4-word block.
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[i] = seed_io[i];
  const u32 *coeff_words = reinterpret_cast<const u32 *>(&result[0]);
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    block[STATE_SIZE + i] = coeff_words[i];
  compress<false>(state, t, block, BLOCK_SIZE);

#pragma unroll
  for (unsigned i = 0; i < 4; i++)
    block[i] = coeff_words[STATE_SIZE + i];
#pragma unroll
  for (unsigned i = 4; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, 4);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_io[i] = state[i];

  // Extract the fold challenge from the first 4 words of the new seed.
  *challenge_out = e4_from_raw_u32x4(state);
}

// ---------------------------------------------------------------------------
// Assemble query indexes from a stream of random u32 words (device-side).
//
// Mirrors the host `BitSource` + `assemble_query_index(log_domain_size, ...)`
// chain used in WHIR PoW query derivation. The bit stream is LE-packed across
// u32 words; the first 32 bits are skipped (they were consumed as the PoW
// header in `draw_query_bits_after_verified_pow`). Each query reads
// `log_domain_size` contiguous bits.
//
// Buffer contracts:
// - `raw_bits`: padded u32 buffer (matches the squeeze output size, at least
//   `ceil((32 + num_queries * log_domain_size) / 32)` words).
// - `indexes_out`: `num_queries` u32 indexes, one per thread.
// ---------------------------------------------------------------------------
EXTERN __global__ void ab_assemble_query_indexes_kernel(const u32 *raw_bits, u32 *indexes_out, const unsigned num_queries, const unsigned log_domain_size) {
  const unsigned idx = blockIdx.x * blockDim.x + threadIdx.x;
  if (idx >= num_queries)
    return;
  // Skip the first 32 bits (PoW header word); each subsequent query consumes
  // log_domain_size bits.
  const unsigned start_bit = 32u + idx * log_domain_size;
  u32 result = 0;
  for (unsigned i = 0; i < log_domain_size; i++) {
    const unsigned bit_pos = start_bit + i;
    const unsigned word_idx = bit_pos >> 5;
    const unsigned bit_idx = bit_pos & 31u;
    const u32 bit = (raw_bits[word_idx] >> bit_idx) & 1u;
    result |= bit << i;
  }
  indexes_out[idx] = result;
}

} // namespace airbender::ops::blake2s
