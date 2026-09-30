#include <common.cuh>
#include <hash.cuh>
#include <primitives/field.cuh>
#include <primitives/memory.cuh>
#include <whir_leaf_transform.cuh>

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using ::airbender::hash::BLOCK_SIZE;
using ::airbender::hash::digest;
using ::airbender::hash::FULL_MASK;
using ::airbender::hash::LOG_WARP_SIZE;
using ::airbender::hash::STATE_SIZE;
using ::airbender::hash::WARP_MASK;
using ::airbender::ntt::params_inverse_power_source;
using ::airbender::ntt::whir_leaf_transform_params;

namespace airbender::whir {

// Dynamic shared memory of every kernel in this unit (sized by the launcher).
extern __shared__ __align__(16) uint8_t residue_smem[];

// Residue-polynomial commitment of a recursive WHIR oracle.
//
// f(X) = sum_r X^r P_r(X^V) with P_r(Y) = sum_t a[r + V t] Y^t, M = N / V.
// The committed coefficient leaf of point x = omega_{N C}^c omega_N^{row + k M}
// (row `row` of natural coset `c`) holds slot r = P_r(x^V), and
// x^V = omega_{M C}^c * omega_M^row. `coeffs` is the existing bit-reversed
// monomial copy: four BF limb columns of N, each bit-reversed over log N, so
// block b (rows b*M .. (b+1)*M) of a limb column is the bit-reversed
// coefficient vector of P_{bitrev_V(b)}.
//
// Tree leaf index = bitrev_C(c) * M + row; boundary root k covers tree leaves
// 32k .. 32k+31. Leaf bytes: slot-major, limb-minor raw Montgomery words, the
// stream `hash_leaf_from_ntt` / `absorb_e4_stream` absorb.

// Forward power omega^e (e reduced mod 2^omega_log_order) through the inverse
// power tables of `whir_leaf_transform_params`.
DEVICE_FORCEINLINE bf omega_forward_power(const params_inverse_power_source &inverse_powers, const unsigned exponent_mask, const unsigned exponent) {
  return inverse_powers.get((0u - exponent) & exponent_mask);
}

DEVICE_FORCEINLINE void store_root(u32 *boundary_roots, const unsigned root_index, const u32 state[STATE_SIZE]) {
  digest root;
#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    root.words[i] = state[i];
  store_cs(reinterpret_cast<digest *>(boundary_roots) + root_index, root);
}

// Commit-only reduction for a whole coset block. Reuse the NTT tile as two
// limb-major digest layers: 2 * STATE_SIZE * M words fit in its 17.5 * M
// words. Compact the active parents at each level so fewer warps execute the
// compression. The ping-pong layers avoid overwriting another warp's inputs.
DEVICE_FORCEINLINE void reduce_block_subtrees(u32 state[STATE_SIZE]) {
  const unsigned tid = threadIdx.x;
  const unsigned m = blockDim.x;
  u32 *src = reinterpret_cast<u32 *>(residue_smem);
  u32 *dst = src + STATE_SIZE * m;
#pragma unroll
  for (unsigned word = 0; word < STATE_SIZE; word++)
    src[word * m + tid] = state[word];
  __syncthreads();
#pragma unroll
  for (unsigned layer = 0; layer < LOG_WARP_SIZE; layer++) {
    const unsigned parents = m >> (layer + 1);
    if (tid < parents) {
      u32 block[BLOCK_SIZE];
#pragma unroll
      for (unsigned word = 0; word < STATE_SIZE; word++) {
        block[word] = src[word * m + 2 * tid];
        block[word + STATE_SIZE] = src[word * m + 2 * tid + 1];
      }
      ::airbender::hash::initialize(state);
      u32 t = 0;
      ::airbender::hash::compress<true>(state, t, block, BLOCK_SIZE);
#pragma unroll
      for (unsigned word = 0; word < STATE_SIZE; word++)
        dst[word * m + tid] = state[word];
    }
    __syncthreads();
    u32 *swap = src;
    src = dst;
    dst = swap;
  }
}

// First two layers use compact shared-memory parents. After their last CTA
// barrier, warp zero owns all remaining parents for any M in [32, 256].
// Its four adjacent lanes finish one 32-leaf subtree; compact lane 4*r into
// lane r so callers keep the existing thread-r root store convention.
DEVICE_FORCEINLINE void reduce_block_subtrees_hybrid(u32 state[STATE_SIZE]) {
  const unsigned tid = threadIdx.x;
  const unsigned m = blockDim.x;
  u32 *src = reinterpret_cast<u32 *>(residue_smem);
  u32 *dst = src + STATE_SIZE * m;
#pragma unroll
  for (unsigned word = 0; word < STATE_SIZE; word++)
    src[word * m + tid] = state[word];
  __syncthreads();
#pragma unroll
  for (unsigned layer = 0; layer < 2; layer++) {
    const unsigned parents = m >> (layer + 1);
    if (tid < parents) {
      u32 block[BLOCK_SIZE];
#pragma unroll
      for (unsigned word = 0; word < STATE_SIZE; word++) {
        block[word] = src[word * m + 2 * tid];
        block[word + STATE_SIZE] = src[word * m + 2 * tid + 1];
      }
      ::airbender::hash::initialize(state);
      u32 t = 0;
      ::airbender::hash::compress<true>(state, t, block, BLOCK_SIZE);
#pragma unroll
      for (unsigned word = 0; word < STATE_SIZE; word++)
        dst[word * m + tid] = state[word];
    }
    __syncthreads();
    u32 *swap = src;
    src = dst;
    dst = swap;
  }
  // No CTA barriers follow. Every lane of warp zero stays active, including
  // padding lanes for M < 256, so all FULL_MASK shuffles below are valid.
  if (tid >= 32)
    return;
  u32 block[BLOCK_SIZE];
#pragma unroll
  for (unsigned word = 0; word < STATE_SIZE; word++)
    state[word] = 0;
  if (tid < (m >> 3)) {
#pragma unroll
    for (unsigned word = 0; word < STATE_SIZE; word++) {
      block[word] = src[word * m + 2 * tid];
      block[word + STATE_SIZE] = src[word * m + 2 * tid + 1];
    }
    ::airbender::hash::initialize(state);
    u32 t = 0;
    ::airbender::hash::compress<true>(state, t, block, BLOCK_SIZE);
  }
#pragma unroll
  for (unsigned layer = 0; layer < 2; layer++) {
    const bool take_other_first = (tid >> layer) & 1;
#pragma unroll
    for (unsigned word = 0; word < STATE_SIZE; word++) {
      const u32 other = __shfl_xor_sync(FULL_MASK, state[word], 1u << layer);
      block[word] = take_other_first ? other : state[word];
      block[word + STATE_SIZE] = take_other_first ? state[word] : other;
    }
    ::airbender::hash::initialize(state);
    u32 t = 0;
    ::airbender::hash::compress<true>(state, t, block, BLOCK_SIZE);
  }
#pragma unroll
  for (unsigned word = 0; word < STATE_SIZE; word++)
    state[word] = __shfl_sync(FULL_MASK, state[word], (4u * tid) & WARP_MASK);
}

// ---------------------------------------------------------------------------
// Sub-warp family: M = N / V <= 16. One warp owns one 32-leaf subtree, which
// spans 32 / M bit-reverse-adjacent cosets. M = 16 runs a shuffle DIT per
// half-warp coset; smaller M evaluates its V slots by Horner (M = 2 is the
// affine form). Both read the block-shared coefficient copy in smem.
// ---------------------------------------------------------------------------

template <bool QUERY>
DEVICE_FORCEINLINE void hash_residue_leaf_subwarp(const bf *coef_smem, const params_inverse_power_source &inverse_powers, const unsigned log_n,
                                                  const unsigned log_c, const unsigned log_v, const unsigned tree_leaf, bf *leaf_out, u32 state[STATE_SIZE]) {
  const unsigned order = inverse_powers.params.omega_log_order;
  const unsigned exponent_mask = (1u << order) - 1u;
  const unsigned log_m = log_n - log_v;
  const unsigned m = 1u << log_m;
  const unsigned n = 1u << log_n;
  const unsigned v = 1u << log_v;
  const unsigned bitrev_coset = tree_leaf >> log_m;
  const unsigned row = tree_leaf & (m - 1u);
  const unsigned coset = bitreverse_low_bits(bitrev_coset, log_c);
  const unsigned y_exponent = (coset << (order - log_m - log_c)) + (row << (order - log_m));
  const bf y = omega_forward_power(inverse_powers, exponent_mask, y_exponent);

  ::airbender::hash::initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];
  for (unsigned s0 = 0; s0 < v; s0 += 4) {
#pragma unroll
    for (unsigned j = 0; j < 4; j++) {
      const unsigned s = s0 + j;
      if (s < v) {
        const unsigned base = bitreverse_low_bits(s, log_v) << log_m;
        bf acc[4];
        unsigned p = base + bitreverse_low_bits(m - 1u, log_m);
#pragma unroll
        for (unsigned l = 0; l < 4; l++)
          acc[l] = coef_smem[l * n + p];
        for (unsigned tt = m - 1u; tt-- > 0;) {
          p = base + bitreverse_low_bits(tt, log_m);
#pragma unroll
          for (unsigned l = 0; l < 4; l++)
            acc[l] = bf::fma(acc[l], y, coef_smem[l * n + p]);
        }
#pragma unroll
        for (unsigned l = 0; l < 4; l++) {
          block[4 * j + l] = bf::into_raw_u32(acc[l]);
          if constexpr (QUERY) {
            if (leaf_out != nullptr)
              leaf_out[4 * s + l] = acc[l];
          }
        }
      } else {
#pragma unroll
        for (unsigned l = 0; l < 4; l++)
          block[4 * j + l] = 0;
      }
    }
    const unsigned remaining = v - s0;
    if (remaining <= 4)
      ::airbender::hash::compress<true>(state, t, block, 4 * remaining);
    else
      ::airbender::hash::compress<false>(state, t, block, BLOCK_SIZE);
  }
}

// M = 16 residue transform for the sub-warp family. The 16 rows of one coset
// are the 16 lanes of a half-warp. Every lane holds bit-reversed position
// `row` of each (residue, limb) column, scales it by g^{bitrev_4(row)} for
// g = omega_{M C}^c, and a four-stage DIT over `__shfl_xor_sync` leaves lane
// `row` holding P_s(y_row) for that column: its own leaf slot, absorbed into
// the Blake block directly. Replaces the O(M^2) Horner evaluation at M = 16.
template <bool QUERY, unsigned LOG_M>
DEVICE_FORCEINLINE void hash_residue_leaf_subwarp_shuffle(const bf *coef_smem, const params_inverse_power_source &inverse_powers, const unsigned log_n,
                                                          const unsigned log_c, const unsigned log_v, const unsigned tree_leaf, bf *leaf_out,
                                                          u32 state[STATE_SIZE]) {
  constexpr unsigned M = 1u << LOG_M;
  const unsigned order = inverse_powers.params.omega_log_order;
  const unsigned exponent_mask = (1u << order) - 1u;
  const unsigned n = 1u << log_n;
  const unsigned v = 1u << log_v;
  const unsigned row = tree_leaf & (M - 1u);
  const unsigned coset = bitreverse_low_bits(tree_leaf >> LOG_M, log_c);
  const unsigned natural_t = bitreverse_low_bits(row, LOG_M);
  const bf scale = omega_forward_power(inverse_powers, exponent_mask, (coset * natural_t) << (order - LOG_M - log_c));
  // Stage j pairs positions (i0, i0 + 2^j) with twiddle omega_M^{k << (LOG_M - 1 - j)},
  // k = i0 & (2^j - 1) = row & (2^j - 1) for both lanes of the pair. Stage 0 has k = 0.
  bf twiddles[LOG_M];
#pragma unroll
  for (unsigned stage = 1; stage < LOG_M; stage++) {
    const unsigned k = row & ((1u << stage) - 1u);
    twiddles[stage] = omega_forward_power(inverse_powers, exponent_mask, (k << (LOG_M - 1u - stage)) << (order - LOG_M));
  }
  twiddles[0] = bf::ONE();

  ::airbender::hash::initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];
  for (unsigned s0 = 0; s0 < v; s0 += 4) {
#pragma unroll
    for (unsigned j = 0; j < 4; j++) {
      const unsigned s = s0 + j;
      if (s < v) {
        const unsigned base = bitreverse_low_bits(s, log_v) << LOG_M;
#pragma unroll
        for (unsigned l = 0; l < 4; l++) {
          bf x = bf::mul(coef_smem[l * n + base + row], scale);
#pragma unroll
          for (unsigned stage = 0; stage < LOG_M; stage++) {
            const unsigned half = 1u << stage;
            const bf other = bf::from_reduced_raw_repr(__shfl_xor_sync(FULL_MASK, bf::into_raw_u32(x), half));
            if (stage == 0) {
              x = (row & half) ? bf::sub(other, x) : bf::add(x, other);
            } else if (row & half) {
              x = bf::sub(other, bf::mul(x, twiddles[stage]));
            } else {
              x = bf::add(x, bf::mul(other, twiddles[stage]));
            }
          }
          block[4 * j + l] = bf::into_raw_u32(x);
          if constexpr (QUERY) {
            if (leaf_out != nullptr)
              leaf_out[4 * s + l] = x;
          }
        }
      } else {
#pragma unroll
        for (unsigned l = 0; l < 4; l++)
          block[4 * j + l] = 0;
      }
    }
    const unsigned remaining = v - s0;
    if (remaining <= 4)
      ::airbender::hash::compress<true>(state, t, block, 4 * remaining);
    else
      ::airbender::hash::compress<false>(state, t, block, BLOCK_SIZE);
  }
}

template <bool QUERY>
DEVICE_FORCEINLINE void hash_residue_leaf_subwarp_dispatch(const bf *coef_smem, const params_inverse_power_source &inverse_powers, const unsigned log_n,
                                                           const unsigned log_c, const unsigned log_v, const unsigned tree_leaf, bf *leaf_out,
                                                           u32 state[STATE_SIZE]) {
  if (log_n - log_v == 4)
    hash_residue_leaf_subwarp_shuffle<QUERY, 4>(coef_smem, inverse_powers, log_n, log_c, log_v, tree_leaf, leaf_out, state);
  else if (log_n - log_v == 3)
    hash_residue_leaf_subwarp_shuffle<QUERY, 3>(coef_smem, inverse_powers, log_n, log_c, log_v, tree_leaf, leaf_out, state);
  else
    hash_residue_leaf_subwarp<QUERY>(coef_smem, inverse_powers, log_n, log_c, log_v, tree_leaf, leaf_out, state);
}

// The commit-only reduction compacts eight subtrees across a block. All
// threads participate in barriers, including unused warps in the last block.
EXTERN __launch_bounds__(256) __global__
    void ab_whir_residue_commit_subwarp_cooperative_kernel(const bf *coeffs, u32 *boundary_roots, const whir_leaf_transform_params transform_params,
                                                           const unsigned log_n, const unsigned log_c, const unsigned log_v, const unsigned subtrees_count) {
  bf *coef_smem = reinterpret_cast<bf *>(residue_smem);
  const unsigned coef_count = 4u << log_n;
  for (unsigned i = threadIdx.x; i < coef_count; i += blockDim.x)
    coef_smem[i] = load_ca(coeffs + i);
  __syncthreads();
  const unsigned roots_per_block = blockDim.x >> LOG_WARP_SIZE;
  const unsigned root_base = blockIdx.x * roots_per_block;
  const unsigned subtree = root_base + (threadIdx.x >> LOG_WARP_SIZE);
  const unsigned tree_leaf = (subtree << LOG_WARP_SIZE) | (threadIdx.x & WARP_MASK);
  const params_inverse_power_source inverse_powers{transform_params};
  u32 state[STATE_SIZE] = {};
  if (subtree < subtrees_count)
    hash_residue_leaf_subwarp_dispatch<false>(coef_smem, inverse_powers, log_n, log_c, log_v, tree_leaf, nullptr, state);
  // Finish all coefficient reads before reusing shared memory for digests.
  __syncthreads();
  reduce_block_subtrees(state);
  if (threadIdx.x < roots_per_block && root_base + threadIdx.x < subtrees_count)
    store_root(boundary_roots, root_base + threadIdx.x, state);
}

EXTERN __launch_bounds__(32) __global__
    void ab_whir_residue_query_subwarp_kernel(const bf *coeffs, const u32 *partial_tree, bf *leaves, u32 *paths,
                                              const whir_leaf_transform_params transform_params, const unsigned log_n, const unsigned log_c,
                                              const unsigned log_v, const unsigned log_total_leaves, const unsigned layers_count, const unsigned *indexes,
                                              const unsigned indexes_count) {
  const unsigned query = blockIdx.x;
  if (query >= indexes_count)
    return;
  bf *coef_smem = reinterpret_cast<bf *>(residue_smem);
  const unsigned coef_count = 4u << log_n;
  for (unsigned i = threadIdx.x; i < coef_count; i += blockDim.x)
    coef_smem[i] = load_ca(coeffs + i);
  __syncthreads();
  const unsigned lane = threadIdx.x & WARP_MASK;
  const unsigned q = indexes[query];
  const unsigned tree_leaf = (q & ~WARP_MASK) | lane;
  const bool is_output_lane = tree_leaf == q;
  bf *leaf_out = is_output_lane ? leaves + (static_cast<size_t>(query) << (log_v + 2)) : nullptr;
  const params_inverse_power_source inverse_powers{transform_params};
  u32 state[STATE_SIZE];
  hash_residue_leaf_subwarp_dispatch<true>(coef_smem, inverse_powers, log_n, log_c, log_v, tree_leaf, leaf_out, state);
  u32 *merkle_paths = paths + static_cast<size_t>(query) * layers_count * STATE_SIZE;
  ::airbender::hash::collect_merkle_path_warp(state, merkle_paths, STATE_SIZE, lane, is_output_lane, q, log_total_leaves, layers_count, partial_tree);
}

// ---------------------------------------------------------------------------
// Block family: 32 <= M <= 256, V >= 4. One block of M threads owns one coset
// (thread = row = leaf). Each step scales and transforms four residue
// polynomials (16 BF columns of M) in smem, then every leaf absorbs exactly
// one Blake2s block of those four slots; V / 4 steps per coset. Commitment
// reduces the block cooperatively to one boundary root per 32 rows.
// ---------------------------------------------------------------------------

constexpr unsigned BLOCK_FAMILY_TILE_COLUMNS = BLOCK_SIZE;

template <bool QUERY>
DEVICE_FORCEINLINE void hash_residue_coset_block(const bf *coeffs, const params_inverse_power_source &inverse_powers, const unsigned log_n,
                                                 const unsigned log_c, const unsigned log_v, const unsigned coset, bf *leaf_out, u32 state[STATE_SIZE]) {
  const unsigned order = inverse_powers.params.omega_log_order;
  const unsigned exponent_mask = (1u << order) - 1u;
  const unsigned log_m = log_n - log_v;
  const unsigned m = 1u << log_m;
  const unsigned n = 1u << log_n;
  const unsigned v = 1u << log_v;
  const unsigned tid = threadIdx.x;
  bf *tile = reinterpret_cast<bf *>(residue_smem);
  bf *scale = tile + BLOCK_FAMILY_TILE_COLUMNS * m;
  bf *twiddles = scale + m;

  // scale[q] = g^{bitrev_M(q)} for g = omega_{M C}^c: the coset factor of the
  // coefficient stored at bit-reversed position q (natural index bitrev_M(q)).
  {
    const unsigned natural_t = bitreverse_low_bits(tid, log_m);
    const unsigned scale_exponent = (coset * natural_t) << (order - log_m - log_c);
    scale[tid] = omega_forward_power(inverse_powers, exponent_mask, scale_exponent);
  }
  if (tid < (m >> 1))
    twiddles[tid] = omega_forward_power(inverse_powers, exponent_mask, tid << (order - log_m));
  __syncthreads();

  ::airbender::hash::initialize(state);
  u32 t = 0;
  const unsigned steps = v >> 2;
  const unsigned half_m = m >> 1;
  const unsigned pair = tid & (half_m - 1u);
  const unsigned column_parity = tid >> (log_m - 1u);
  for (unsigned b = 0; b < steps; b++) {
#pragma unroll
    for (unsigned j = 0; j < 4; j++) {
      const unsigned block_index = bitreverse_low_bits(4 * b + j, log_v);
      const bf *src = coeffs + (block_index << log_m) + tid;
#pragma unroll
      for (unsigned l = 0; l < 4; l++)
        tile[((4 * j + l) << log_m) + tid] = bf::mul(load_ca(src + l * n), scale[tid]);
    }
    __syncthreads();
    // Radix-2 DIT over the 16 columns: bit-reversed input, natural output.
    for (unsigned stage = 0; stage < log_m; stage++) {
      const unsigned half = 1u << stage;
      const unsigned group = pair >> stage;
      const unsigned k = pair & (half - 1u);
      const unsigned i0 = (group << (stage + 1u)) + k;
      const unsigned i1 = i0 + half;
      const bf w = twiddles[k << (log_m - 1u - stage)];
#pragma unroll
      for (unsigned i = 0; i < BLOCK_FAMILY_TILE_COLUMNS / 2; i++) {
        bf *column = tile + ((2 * i + column_parity) << log_m);
        const bf u = column[i0];
        const bf x = bf::mul(column[i1], w);
        column[i0] = bf::add(u, x);
        column[i1] = bf::sub(u, x);
      }
      __syncthreads();
    }
    u32 block[BLOCK_SIZE];
#pragma unroll
    for (unsigned w = 0; w < BLOCK_SIZE; w++) {
      const bf value = tile[(w << log_m) + tid];
      block[w] = bf::into_raw_u32(value);
      if constexpr (QUERY) {
        if (leaf_out != nullptr)
          leaf_out[BLOCK_SIZE * b + w] = value;
      }
    }
    if (b + 1 == steps)
      ::airbender::hash::compress<true>(state, t, block, BLOCK_SIZE);
    else
      ::airbender::hash::compress<false>(state, t, block, BLOCK_SIZE);
    __syncthreads();
  }
}

EXTERN __launch_bounds__(256) __global__
    void ab_whir_residue_commit_block_kernel(const bf *coeffs, u32 *boundary_roots, const whir_leaf_transform_params transform_params, const unsigned log_n,
                                             const unsigned log_c, const unsigned log_v) {
  const unsigned coset = blockIdx.x;
  const unsigned log_m = log_n - log_v;
  const params_inverse_power_source inverse_powers{transform_params};
  u32 state[STATE_SIZE];
  hash_residue_coset_block<false>(coeffs, inverse_powers, log_n, log_c, log_v, coset, nullptr, state);
  reduce_block_subtrees(state);
  if (threadIdx.x < (1u << (log_m - LOG_WARP_SIZE))) {
    const unsigned root_index = (bitreverse_low_bits(coset, log_c) << (log_m - LOG_WARP_SIZE)) + threadIdx.x;
    store_root(boundary_roots, root_index, state);
  }
}

EXTERN __launch_bounds__(256) __global__
    void ab_whir_residue_commit_block_hybrid_kernel(const bf *coeffs, u32 *boundary_roots, const whir_leaf_transform_params transform_params,
                                                    const unsigned log_n, const unsigned log_c, const unsigned log_v) {
  const unsigned coset = blockIdx.x;
  const unsigned log_m = log_n - log_v;
  const params_inverse_power_source inverse_powers{transform_params};
  u32 state[STATE_SIZE];
  hash_residue_coset_block<false>(coeffs, inverse_powers, log_n, log_c, log_v, coset, nullptr, state);
  reduce_block_subtrees_hybrid(state);
  if (threadIdx.x < (1u << (log_m - LOG_WARP_SIZE))) {
    const unsigned root_index = (bitreverse_low_bits(coset, log_c) << (log_m - LOG_WARP_SIZE)) + threadIdx.x;
    store_root(boundary_roots, root_index, state);
  }
}

// ---------------------------------------------------------------------------
// Radix-4 transform for the M = 256 block family (V = 32). Four radix-4
// stages replace the eight radix-2 stages: each stage pair (2p, 2p+1) is one
// butterfly over positions i0, i0+h, i0+2h, i0+3h with h = 4^p, twiddles
// w1 = omega_{2h}^k, w2 = omega_{4h}^k, w3 = omega_{4h}^{k+h} from the same
// omega_M table (w3 is a table entry, so the field has no free omega_4
// rotation). Per element this is 8 shared-memory operations and 4 barriers per
// step instead of 16 and 8; stage pair 0 reads and writes its four consecutive
// positions as one 16-byte vector so the stride-4 pattern stays conflict-free.
// Loads, scaling, the absorb order and the cooperative reduce are unchanged,
// so leaf bytes and roots are identical to the radix-2 kernel.
DEVICE_FORCEINLINE void hash_residue_coset_block_radix4_m256_unity(const bf *coeffs, const params_inverse_power_source &inverse_powers, const unsigned log_n,
                                                                   const unsigned log_c, const unsigned log_v, const unsigned coset, u32 state[STATE_SIZE]) {
  constexpr unsigned LOG_M = 8;
  constexpr unsigned M = 1u << LOG_M;
  constexpr unsigned COLUMNS = BLOCK_FAMILY_TILE_COLUMNS;
  constexpr unsigned QUADS = M / 4;
  constexpr unsigned LOG_QUADS = LOG_M - 2;
  constexpr unsigned COLUMN_GROUPS = M / QUADS;
  constexpr unsigned COLUMNS_PER_THREAD = COLUMNS / COLUMN_GROUPS;
  static_assert(COLUMN_GROUPS * QUADS == M);
  static_assert(COLUMNS_PER_THREAD * COLUMN_GROUPS == COLUMNS);
  const unsigned order = inverse_powers.params.omega_log_order;
  const unsigned exponent_mask = (1u << order) - 1u;
  const unsigned n = 1u << log_n;
  const unsigned v = 1u << log_v;
  const unsigned tid = threadIdx.x;
  bf *tile = reinterpret_cast<bf *>(residue_smem);
  bf *scale = tile + COLUMNS * M;
  bf *twiddles = scale + M;

  {
    const unsigned natural_t = bitreverse_low_bits(tid, LOG_M);
    const unsigned scale_exponent = (coset * natural_t) << (order - LOG_M - log_c);
    scale[tid] = omega_forward_power(inverse_powers, exponent_mask, scale_exponent);
  }
  if (tid < (M >> 1))
    twiddles[tid] = omega_forward_power(inverse_powers, exponent_mask, tid << (order - LOG_M));
  __syncthreads();

  ::airbender::hash::initialize(state);
  u32 t = 0;
  const unsigned steps = v >> 2;
  const unsigned quad = tid & (QUADS - 1u);
  const unsigned column_group = tid >> LOG_QUADS;
  for (unsigned b = 0; b < steps; b++) {
#pragma unroll
    for (unsigned j = 0; j < 4; j++) {
      const unsigned block_index = bitreverse_low_bits(4 * b + j, log_v);
      const bf *src = coeffs + (block_index << LOG_M) + tid;
#pragma unroll
      for (unsigned l = 0; l < 4; l++)
        tile[((4 * j + l) << LOG_M) + tid] = bf::mul(load_ca(src + l * n), scale[tid]);
    }
    __syncthreads();
#pragma unroll
    for (unsigned p = 0; p < LOG_M / 2; p++) {
      const unsigned h = 1u << (2 * p);
      const unsigned group = quad >> (2 * p);
      const unsigned k = quad & (h - 1u);
      const unsigned i0 = (group << (2 * p + 2)) + k;
      const bf w1 = twiddles[k << (LOG_M - 1u - 2 * p)];
      const bf w2 = twiddles[k << (LOG_M - 2u - 2 * p)];
      const bf w3 = twiddles[(k + h) << (LOG_M - 2u - 2 * p)];
#pragma unroll
      for (unsigned i = 0; i < COLUMNS_PER_THREAD; i++) {
        bf *column = tile + ((column_group + COLUMN_GROUPS * i) << LOG_M);
        bf a, bq, c, d;
        if (p == 0) {
          const uint4 packed = *reinterpret_cast<const uint4 *>(column + i0);
          a = bf(packed.x);
          bq = bf(packed.y);
          c = bf(packed.z);
          d = bf(packed.w);
        } else {
          a = column[i0];
          bq = column[i0 + h];
          c = column[i0 + 2 * h];
          d = column[i0 + 3 * h];
        }
        bf out0, out1, out2, out3;
        if (p == 0) {
          // k == 0: w1 == w2 == 1 (tw[0]); only w3 = tw[M / 4] multiplies.
          const bf a1 = bf::add(a, bq);
          const bf b1 = bf::sub(a, bq);
          const bf c1 = bf::add(c, d);
          const bf d1 = bf::sub(c, d);
          const bf w3d = bf::mul(d1, w3);
          out0 = bf::add(a1, c1);
          out1 = bf::add(b1, w3d);
          out2 = bf::sub(a1, c1);
          out3 = bf::sub(b1, w3d);
        } else {
          const bf wb = bf::mul(bq, w1);
          const bf wd = bf::mul(d, w1);
          const bf a1 = bf::add(a, wb);
          const bf b1 = bf::sub(a, wb);
          const bf c1 = bf::add(c, wd);
          const bf d1 = bf::sub(c, wd);
          const bf w2c = bf::mul(c1, w2);
          const bf w3d = bf::mul(d1, w3);
          out0 = bf::add(a1, w2c);
          out1 = bf::add(b1, w3d);
          out2 = bf::sub(a1, w2c);
          out3 = bf::sub(b1, w3d);
        }
        if (p == 0) {
          *reinterpret_cast<uint4 *>(column + i0) = make_uint4(bf::into_raw_u32(out0), bf::into_raw_u32(out1), bf::into_raw_u32(out2), bf::into_raw_u32(out3));
        } else {
          column[i0] = out0;
          column[i0 + h] = out1;
          column[i0 + 2 * h] = out2;
          column[i0 + 3 * h] = out3;
        }
      }
      __syncthreads();
    }
    u32 block[BLOCK_SIZE];
#pragma unroll
    for (unsigned w = 0; w < BLOCK_SIZE; w++) {
      const bf value = tile[(w << LOG_M) + tid];
      block[w] = bf::into_raw_u32(value);
    }
    if (b + 1 == steps)
      ::airbender::hash::compress<true>(state, t, block, BLOCK_SIZE);
    else
      ::airbender::hash::compress<false>(state, t, block, BLOCK_SIZE);
    __syncthreads();
  }
}

// Stage zero skips the runtime multiplies by tw[0] == 1.
EXTERN __launch_bounds__(256) __global__
    void ab_whir_residue_commit_block_radix4_unity_kernel(const bf *coeffs, u32 *boundary_roots, const whir_leaf_transform_params transform_params,
                                                          const unsigned log_n, const unsigned log_c, const unsigned log_v) {
  const unsigned coset = blockIdx.x;
  const unsigned log_m = log_n - log_v;
  const params_inverse_power_source inverse_powers{transform_params};
  u32 state[STATE_SIZE];
  hash_residue_coset_block_radix4_m256_unity(coeffs, inverse_powers, log_n, log_c, log_v, coset, state);
  reduce_block_subtrees(state);
  if (threadIdx.x < (1u << (log_m - LOG_WARP_SIZE))) {
    const unsigned root_index = (bitreverse_low_bits(coset, log_c) << (log_m - LOG_WARP_SIZE)) + threadIdx.x;
    store_root(boundary_roots, root_index, state);
  }
}

EXTERN __launch_bounds__(256) __global__
    void ab_whir_residue_query_block_kernel(const bf *coeffs, const u32 *partial_tree, bf *leaves, u32 *paths,
                                            const whir_leaf_transform_params transform_params, const unsigned log_n, const unsigned log_c, const unsigned log_v,
                                            const unsigned log_total_leaves, const unsigned layers_count, const unsigned *indexes,
                                            const unsigned indexes_count) {
  const unsigned query = blockIdx.x;
  if (query >= indexes_count)
    return;
  const unsigned log_m = log_n - log_v;
  const unsigned m = 1u << log_m;
  const unsigned q = indexes[query];
  const unsigned coset = bitreverse_low_bits(q >> log_m, log_c);
  const unsigned row_q = q & (m - 1u);
  const bool is_output_lane = threadIdx.x == row_q;
  bf *leaf_out = is_output_lane ? leaves + (static_cast<size_t>(query) << (log_v + 2)) : nullptr;
  const params_inverse_power_source inverse_powers{transform_params};
  u32 state[STATE_SIZE];
  hash_residue_coset_block<true>(coeffs, inverse_powers, log_n, log_c, log_v, coset, leaf_out, state);
  const unsigned warp = threadIdx.x >> LOG_WARP_SIZE;
  if (warp != (row_q >> LOG_WARP_SIZE))
    return;
  const unsigned lane = threadIdx.x & WARP_MASK;
  u32 *merkle_paths = paths + static_cast<size_t>(query) * layers_count * STATE_SIZE;
  ::airbender::hash::collect_merkle_path_warp(state, merkle_paths, STATE_SIZE, lane, is_output_lane, q, log_total_leaves, layers_count, partial_tree);
}

} // namespace airbender::whir
