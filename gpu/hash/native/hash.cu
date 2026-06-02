#include "hash.cuh"

namespace airbender::hash {

EXTERN __global__ void ab_blake2s_leaves_kernel(const bf *values, u32 *results, const unsigned log_rows_count, const unsigned cols_count,
                                                const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  const unsigned domain_size = count << log_rows_count;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    const unsigned row = gid + bitreverse_low_bits(row_slot, log_rows_count) * count;
    return col < cols_count ? bf::into_raw_u32(load_cs(values + row + col * domain_size)) : 0;
  };
  digest state;
  u32 block[BLOCK_SIZE];
  initialize(state.words);
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
      compress<true>(state.words, t, block, remaining);
    else
      compress<false>(state.words, t, block, BLOCK_SIZE);
  }
  // Single 256-bit aligned store: STG.E.ENL2.256 on sm_100+ / 2× STG.E.128 on older arch.
  store_cs(reinterpret_cast<digest *>(results) + gid, state);
}

// Multi-coset leaves kernel: hashes `(1 << log_per_coset_count) *
// cosets_in_tile` leaves in one launch. Each coset's leaf inputs and tree
// outputs sit in per-coset slabs offset by `per_coset_values_stride_bf` and
// `per_coset_results_stride_digests` respectively; cosets are independent so
// the kernel just decomposes `gid_global` into `(coset, gid_in_coset)` and
// advances the base pointers by the coset stride.
EXTERN __global__ void ab_blake2s_leaves_multi_coset_kernel(const bf *values, u32 *results, const unsigned log_rows_count, const unsigned cols_count,
                                                            const unsigned log_per_coset_count, const unsigned per_coset_values_stride_bf,
                                                            const unsigned per_coset_results_stride_digests, const unsigned count) {
  const unsigned gid_global = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid_global >= count)
    return;
  const unsigned per_coset_count = 1u << log_per_coset_count;
  const unsigned coset = gid_global >> log_per_coset_count;
  const unsigned gid = gid_global & (per_coset_count - 1u);
  values += static_cast<size_t>(coset) * per_coset_values_stride_bf;
  digest *results_d = reinterpret_cast<digest *>(results) + static_cast<size_t>(coset) * per_coset_results_stride_digests + gid;
  const unsigned row_mask = (1u << log_rows_count) - 1;
  const unsigned domain_size = per_coset_count << log_rows_count;
  auto read = [=](const unsigned offset) {
    const unsigned row_slot = offset & row_mask;
    const unsigned col = offset >> log_rows_count;
    const unsigned row = gid + bitreverse_low_bits(row_slot, log_rows_count) * per_coset_count;
    return col < cols_count ? bf::into_raw_u32(load_cs(values + row + col * domain_size)) : 0;
  };
  digest state;
  u32 block[BLOCK_SIZE];
  initialize(state.words);
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
      compress<true>(state.words, t, block, remaining);
    else
      compress<false>(state.words, t, block, BLOCK_SIZE);
  }
  store_cs(results_d, state);
}

EXTERN __global__ void ab_blake2s_nodes_kernel(const u32 *values, u32 *results, const unsigned count) {
  const unsigned gid = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid >= count)
    return;
  // Input block = 64 B = 2 digests; address is 64-aligned, so load via two 256-bit ops
  // (LDG.E.ENL2.256 on sm_100+ / 2× LDG.E.128 on older) instead of 16× LDG.E.
  const digest *values_d = reinterpret_cast<const digest *>(values) + gid * 2;
  digest *results_d = reinterpret_cast<digest *>(results) + gid;
  digest state;
  digest block[2];
  block[0] = load_cs(values_d);
  block[1] = load_cs(values_d + 1);
  initialize(state.words);
  u32 t = 0;
  compress<true>(state.words, t, reinterpret_cast<const u32 *>(block), BLOCK_SIZE);
  store_cs(results_d, state);
}

// Multi-coset nodes kernel: hashes `(1 << log_per_coset_count) *
// cosets_in_tile` pairs of digests into the same number of output digests.
// Each coset's layer-input and layer-output sit in independent slabs offset
// by `per_coset_values_stride_digests` and `per_coset_results_stride_digests`.
EXTERN __global__ void ab_blake2s_nodes_multi_coset_kernel(const u32 *values, u32 *results, const unsigned log_per_coset_count,
                                                           const unsigned per_coset_values_stride_digests, const unsigned per_coset_results_stride_digests,
                                                           const unsigned count) {
  const unsigned gid_global = threadIdx.x + blockIdx.x * blockDim.x;
  if (gid_global >= count)
    return;
  const unsigned coset = gid_global >> log_per_coset_count;
  const unsigned gid = gid_global & ((1u << log_per_coset_count) - 1u);
  // Each leaf pair is 2 adjacent digests (64 B), 64-aligned at every (coset, gid).
  const digest *values_d = reinterpret_cast<const digest *>(values) + static_cast<size_t>(coset) * per_coset_values_stride_digests + gid * 2;
  digest *results_d = reinterpret_cast<digest *>(results) + static_cast<size_t>(coset) * per_coset_results_stride_digests + gid;
  digest state;
  digest block[2];
  block[0] = load_cs(values_d);
  block[1] = load_cs(values_d + 1);
  initialize(state.words);
  u32 t = 0;
  compress<true>(state.words, t, reinterpret_cast<const u32 *>(block), BLOCK_SIZE);
  store_cs(results_d, state);
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

// Mirror of `GpuChunkedInputDesc` in gpu/circuit_prover/src/ops/blake2s.rs. Holds the
// per-launch chunk source pointer table inline as kernel-arg data so the
// chunked-commit kernel reads `num_chunks` contiguous u32 buffers without an
// auxiliary device allocation. Replaces the host-side concat-into-d_transcript_input
// pack in `prove()`.
constexpr unsigned GKR_CHUNKED_COMMIT_MAX_CHUNKS = 8;

struct gpu_chunked_input_desc {
  u32 num_chunks;
  u32 _pad;
  unsigned long long src_ptrs[GKR_CHUNKED_COMMIT_MAX_CHUNKS];
  u32 chunk_lens[GKR_CHUNKED_COMMIT_MAX_CHUNKS];
};

// commit_initial_chunked: seed_out = Blake2s(chunk_0 || chunk_1 || ... || chunk_{N-1}).
// Identical Blake2s state evolution to `ab_transcript_commit_initial_kernel` for
// the same logical concatenation — Blake2s streams 64-byte (= 16 u32) blocks, so
// chunk boundaries that fall mid-block are handled transparently.
EXTERN __global__ void ab_transcript_commit_initial_chunked_kernel(__grid_constant__ const gpu_chunked_input_desc desc, u32 *seed_out) {
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];
#pragma unroll
  for (unsigned i = 0; i < BLOCK_SIZE; i++)
    block[i] = 0;

  unsigned block_offset = 0;
  unsigned remaining_total = 0;
  for (unsigned c = 0; c < desc.num_chunks; c++)
    remaining_total += desc.chunk_lens[c];

  for (unsigned c = 0; c < desc.num_chunks; c++) {
    const u32 *src = reinterpret_cast<const u32 *>(desc.src_ptrs[c]);
    unsigned chunk_remaining = desc.chunk_lens[c];
    while (chunk_remaining > 0) {
      const unsigned space = BLOCK_SIZE - block_offset;
      const unsigned n = chunk_remaining < space ? chunk_remaining : space;
      for (unsigned i = 0; i < n; i++)
        block[block_offset + i] = src[i];
      block_offset += n;
      src += n;
      chunk_remaining -= n;
      remaining_total -= n;

      if (block_offset == BLOCK_SIZE && remaining_total > 0) {
        compress<false>(state, t, block, BLOCK_SIZE);
#pragma unroll
        for (unsigned i = 0; i < BLOCK_SIZE; i++)
          block[i] = 0;
        block_offset = 0;
      }
    }
  }

  // Zero-pad and finalize.
  for (unsigned i = block_offset; i < BLOCK_SIZE; i++)
    block[i] = 0;
  compress<true>(state, t, block, block_offset);

#pragma unroll
  for (unsigned i = 0; i < STATE_SIZE; i++)
    seed_out[i] = state[i];
}

// commit_initial: seed_out = Blake2s(input). Mirrors host `Transcript::commit_initial(input)` —
// no prior seed; the entire `input` block is absorbed from the IV.
// seed_out: STATE_SIZE u32 words, written with the resulting seed.
// input:    input_len u32 words to absorb.
EXTERN __global__ void ab_transcript_commit_initial_kernel(u32 *seed_out, const u32 *input, const unsigned input_len) {
  u32 state[STATE_SIZE];
  initialize(state);
  u32 t = 0;
  u32 block[BLOCK_SIZE];
#pragma unroll
  for (unsigned i = 0; i < BLOCK_SIZE; i++)
    block[i] = 0;

  unsigned block_offset = 0;
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
    seed_out[i] = state[i];
}

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

} // namespace airbender::hash
