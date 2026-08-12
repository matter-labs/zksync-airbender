#pragma once

#include "primitives/field.cuh"

namespace airbender::hash {

using namespace ::airbender::primitives::field;

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

// 7-round reduced Blake2s. Must match the host prover's
// USE_REDUCED_BLAKE2_ROUNDS (prover::definitions): both sides hash the same
// transcript, so this is a cross-language parity constant, not a tunable.
// SIGMAS below stays the full 10-round schedule; only the first ROUNDS rows
// are consumed.
constexpr unsigned ROUNDS = 7;
constexpr unsigned STATE_SIZE = 8;
constexpr unsigned BLOCK_SIZE = 16;
constexpr unsigned LOG_WARP_SIZE = 5;
constexpr unsigned WARP_MASK = (1u << LOG_WARP_SIZE) - 1;
constexpr u32 FULL_MASK = 0xffffffff;

// 32-byte aligned digest view. Used at every gmem digest boundary so the
// `load`/`store` PTX dispatch picks the v8 (256-bit) path: one
// `ld/st.global.X.v4.b64` on sm_100+ (PTX 8.8) or two `ld/st.global.X.v4.u32`
// on older arch — replacing 8 separate scalar LDG.E/STG.E instructions.
// `operator[]` keeps existing `state[i]` indexing working unchanged inside
// `compress` and elsewhere.
struct __align__(32) digest {
  u32 words[STATE_SIZE];
  DEVICE_FORCEINLINE u32 &operator[](unsigned i) { return words[i]; }
  DEVICE_FORCEINLINE u32 operator[](unsigned i) const { return words[i]; }
};
static_assert(sizeof(digest) == 32 && alignof(digest) == 32, "digest must be 32 B / 32-aligned for the v8 PTX path");
static_assert(std::is_same_v<typename ::airbender::primitives::memory::load_unit<digest>::type, ::airbender::primitives::ptx::u32x8>,
              "load_unit<digest> must resolve to u32x8 to engage the v8 PTX path");
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

// Re-export gpu_core's guarded bit-reversal (common.cuh) into this namespace so
// circuit_prover's leaves.cu alias (`using ::airbender::hash::bitreverse_low_bits;`)
// keeps resolving.
using ::bitreverse_low_bits;

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

// Streaming Blake2s absorb of `values_count` u32 words supplied by
// `read(offset)`, finalizing into `state`. `read` is a functor
// `u32(unsigned)`; offsets past the logical input (reached inside the final
// partial block) must return 0. Mirrors the host Blake2sState absorb /
// absorb_final_block chunking over 16-word blocks.
template <typename Read> DEVICE_FORCEINLINE void absorb_stream(u32 state[STATE_SIZE], u32 &t, const unsigned values_count, Read read) {
  u32 block[BLOCK_SIZE];
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
}

// `values_count` counts E4 values, not base-field words.
template <typename ReadE4> DEVICE_FORCEINLINE void absorb_e4_stream(u32 state[STATE_SIZE], u32 &t, const unsigned values_count, ReadE4 read_e4) {
  constexpr unsigned E4S_PER_BLOCK = BLOCK_SIZE / 4;
  u32 block[BLOCK_SIZE];
  unsigned value_offset = 0;
  while (value_offset < values_count) {
    const unsigned remaining = values_count - value_offset;
    const bool is_final_block = remaining <= E4S_PER_BLOCK;
#pragma unroll
    for (unsigned i = 0; i < E4S_PER_BLOCK; i++) {
      const e4 value = i < remaining ? read_e4(value_offset + i) : e4::ZERO();
#pragma unroll
      for (unsigned coeff = 0; coeff < 4; coeff++)
        block[4 * i + coeff] = bf::into_raw_u32(value.base_coefficient_from_flat_idx(coeff));
    }
    const unsigned consumed_values = remaining < E4S_PER_BLOCK ? remaining : E4S_PER_BLOCK;
    value_offset += E4S_PER_BLOCK;
    if (is_final_block)
      compress<true>(state, t, block, consumed_values * 4);
    else
      compress<false>(state, t, block, BLOCK_SIZE);
  }
}

// Rebuilds the bottom five layers with warp shuffles before walking the cached tree.
DEVICE_FORCEINLINE void collect_merkle_path_warp(u32 state[STATE_SIZE], u32 *merkle_paths, const unsigned layer_stride_words, const unsigned lane_idx,
                                                 const bool is_output_lane, const unsigned query_index, const unsigned log_total_leaves_count,
                                                 const unsigned layers_count, const u32 *tree_bottom) {
  u32 block[BLOCK_SIZE];
#pragma unroll
  for (unsigned layer = 0; layer < LOG_WARP_SIZE; layer++) {
    digest other_state;
    const bool take_other_first = (lane_idx >> layer) & 1;
#pragma unroll
    for (unsigned i = 0; i < STATE_SIZE; i++) {
      other_state[i] = __shfl_xor_sync(FULL_MASK, state[i], 1 << layer);
      if (take_other_first) {
        block[i] = other_state[i];
        block[i + STATE_SIZE] = state[i];
      } else {
        block[i] = state[i];
        block[i + STATE_SIZE] = other_state[i];
      }
    }
    if (is_output_lane)
      ::airbender::primitives::memory::store_cs(reinterpret_cast<digest *>(merkle_paths), other_state);
    initialize(state);
    u32 t = 0;
    compress<true>(state, t, block, BLOCK_SIZE);
    merkle_paths += layer_stride_words;
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
    merkle_paths_dst += layer_stride_words;
  }
}

} // namespace airbender::hash
