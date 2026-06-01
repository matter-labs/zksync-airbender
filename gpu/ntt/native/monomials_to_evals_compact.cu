#include "ntt.cuh"

// Compact single-launch all-stages-in-block monomials -> natural evals NTT.
//
// One CUDA block per (column, coset) NTT for small `log_n` in [4, 12]. The
// block holds the entire 2^log_n value array in shared memory, fuses the
// coset shift into the bitreversed load, and runs every butterfly stage
// in-block -- sidestepping the multi-pass kernels (which require start_stage
// >= 5). Inputs are bitreversed monomial coefficients; outputs are the
// natural-order evaluations on `coset_index` (encoded via `coset_factor_power`).
//
// Semantics match `ab_copy_scale_bitreversed_coeffs_kernel` +
// `ab_bitreversed_coeffs_to_natural_ntt_stage_kernel` (the single-stage
// fallback used previously), but executed in one launch.
//
// Shared memory is dynamic (`extern __shared__ bf smem[]`): for LOG_N <= 12
// the per-block requirement is <= 16 KB, well within the default cap.
//
// LOG_N >= 13 is covered by the 2-pass-compact-initial path instead: a single
// block per NTT starves SMs once the per-block working set grows, so we
// transition to a multi-block first-K-stages kernel + the existing
// noninitial_8 second pass starting at log_n=13.

namespace airbender::ntt {

// 256 threads is the existing convention. For small LOG_N some threads sit
// idle on every stage (LOG_N=4 has only 8 butterflies), which is fine: this
// kernel exists to eliminate per-stage launch overhead, not to maximize
// occupancy for tiny problems.
constexpr int COMPACT_THREADS = 256;

template <int LOG_N>
DEVICE_FORCEINLINE void monomials_to_evals_all_stages_in_block(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                               const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset,
                                                               const int log_cosets_in_tile) {
  constexpr int N = 1 << LOG_N;
  constexpr int HALF_N = N >> 1;

  // Flat-blockIdx.x layout: blocks_per_ntt = 1 for compact 1-pass, so the flat
  // index packs (coset_in_tile, col_within_tile) only. Input is shared across
  // cosets (same monomial source); output is coset-major with per-coset stride
  // = `num_cols_per_coset` columns (each column is one trace_len-sized block).
  const FlatBlockIndex fi = decompose_flat_1d(0u, static_cast<unsigned>(log_cosets_in_tile));
  gmem_in.add_col(fi.col);
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const int coset_factor_power = (coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift;

  extern __shared__ bf smem[];

  // Load: bitreversed input + fused coset shift (multiply each natural-index
  // coefficient by tau^(coset_index * natural_idx) = w^(coset_factor_power *
  // natural_idx) where tau is the LDE coset generator). Indices are kept in
  // smem in input (bitreversed) order; the natural index is recovered via
  // `bitrev(gid, LOG_N)` for the coset-shift exponent only.
  if (coset_factor_power > 0) {
    for (int gid = threadIdx.x; gid < N; gid += COMPACT_THREADS) {
      bf value = gmem_in.get_at_row(gid);
      const unsigned natural_idx = bitrev(static_cast<unsigned>(gid), LOG_N);
      const bf coset_offset = get_power_from_layers(::ab_ntt_forward_powers, natural_idx * static_cast<unsigned>(coset_factor_power));
      value = bf::mul(value, coset_offset);
      smem[gid] = value;
    }
  } else {
    for (int gid = threadIdx.x; gid < N; gid += COMPACT_THREADS) {
      smem[gid] = gmem_in.get_at_row(gid);
    }
  }
  __syncthreads();

  // Decimation-in-time butterflies. After `stage` stages, smem holds the NTT
  // of size 2^(stage+1) chunks. We mirror
  // `ab_bitreversed_coeffs_to_natural_ntt_stage_kernel`:
  //   pairs_per_group = 1 << stage
  //   group           = pair_idx >> stage
  //   pair            = pair_idx & (pairs_per_group - 1)
  //   left_idx        = group * (pairs_per_group << 1) + pair
  //   right_idx       = left_idx + pairs_per_group
  //   twiddled_diff   = (left - right) * fwd_twiddle(bitrev(group, LOG_N - 1) << (27 - LOG_N))
  //   smem[left]      = left + right
  //   smem[right]     = twiddled_diff  (no twiddle on the final stage)
  //
  // `gid` ranges over [0, HALF_N) butterflies; each thread sweeps strided
  // pairs to cover the half-domain with up to 256 threads.
#pragma unroll
  for (int stage = 0; stage < LOG_N; stage++) {
    const int pairs_per_group = 1 << stage;
    const int pairs_per_group_mask = pairs_per_group - 1;
    for (int gid = threadIdx.x; gid < HALF_N; gid += COMPACT_THREADS) {
      const int group = gid >> stage;
      const int pair = gid & pairs_per_group_mask;
      const int left_idx = (group << (stage + 1)) + pair;
      const int right_idx = left_idx + pairs_per_group;
      bf left = smem[left_idx];
      bf right = smem[right_idx];
      bf twiddled_diff = bf::sub(left, right);
      if (stage + 1 < LOG_N) {
        const unsigned twiddle_power = bitrev(static_cast<unsigned>(group), LOG_N - 1) << (OMEGA_LOG_ORDER - LOG_N);
        twiddled_diff = bf::mul(twiddled_diff, get_forward_twiddle_power(twiddle_power));
      }
      smem[left_idx] = bf::add(left, right);
      smem[right_idx] = twiddled_diff;
    }
    __syncthreads();
  }

  // Store natural-order evals to gmem.
  for (int idx = threadIdx.x; idx < N; idx += COMPACT_THREADS) {
    gmem_out.set_at_row(idx, smem[idx]);
  }
}

// 2 blocks/SM at all supported LOG_N: per-block smem (<= 16 KB) leaves room.
#define DEFINE_COMPACT_KERNEL(LOG_N, MIN_BLOCKS_PER_SM)                                                                                                        \
  EXTERN __launch_bounds__(COMPACT_THREADS, MIN_BLOCKS_PER_SM)                                                                                                 \
  __global__ void ab_monomials_to_evals_all_##LOG_N##_stages_kernel(                                                                                           \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const bool transposed_monomials, const int log_n,                 \
      const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {                                  \
    /* These flags are part of the shared MonomialsToEvalsInitial signature but */                                                                             \
    /* are irrelevant to the compact kernel: log_n is encoded in the template, */                                                                              \
    /* and transposed_monomials is unsupported (asserted host-side). */                                                                                        \
    (void)transposed_monomials;                                                                                                                                \
    (void)log_n;                                                                                                                                               \
    monomials_to_evals_all_stages_in_block<LOG_N>(gmem_in, gmem_out, coset_index_base, coset_factor_shift, num_cols_per_coset, log_cosets_in_tile);            \
  }

DEFINE_COMPACT_KERNEL(4, 2)
DEFINE_COMPACT_KERNEL(5, 2)
DEFINE_COMPACT_KERNEL(6, 2)
DEFINE_COMPACT_KERNEL(7, 2)
DEFINE_COMPACT_KERNEL(8, 2)
DEFINE_COMPACT_KERNEL(9, 2)
DEFINE_COMPACT_KERNEL(10, 2)
DEFINE_COMPACT_KERNEL(11, 2)
DEFINE_COMPACT_KERNEL(12, 2)

#undef DEFINE_COMPACT_KERNEL

// First-K-stages compact NTT for 2-pass plans covering `log_n` in [15, 20].
//
// One block per chunk of `2^LOG_K` consecutive bitreversed inputs of a size-
// `2^log_n` NTT. The block performs the first `LOG_K` butterfly stages of the
// full NTT and writes natural-order partial outputs back to the same `2^LOG_K`
// chunk. The remaining `log_n - LOG_K` stages are handled by a subsequent
// `noninitial_8` pass with `start_stage = LOG_K`.
//
// Differences from the standalone compact kernel above:
//   * `gmem_block_offset = blockIdx.x << LOG_K` selects the chunk this block
//     owns.
//   * The coset shift uses `bitrev(global_bitrev_idx, log_n)` -- the full NTT
//     size -- not `bitrev(local_gid, LOG_K)`.
//   * Twiddles use the global group index
//     `g_global = (blockIdx.x << (LOG_K - 1 - stage)) | g_local`, paired with
//     `bitrev(g_global, log_n - 1) << (OMEGA_LOG_ORDER - log_n)`. The standalone
//     kernel's "skip twiddle on the last stage" optimization does not apply
//     here -- more stages follow in pass 2, so every stage's twiddle is needed.
//   * `transposed_monomials` is unsupported (asserted host-side).
template <int LOG_K>
DEVICE_FORCEINLINE void monomials_to_evals_first_stages_in_block(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                 const int log_n, const int coset_index_base, const int coset_factor_shift,
                                                                 const int num_cols_per_coset, const int log_cosets_in_tile) {
  constexpr int K_VALS = 1 << LOG_K;
  constexpr int HALF_K = K_VALS >> 1;

  // Flat-blockIdx.x layout: gridDim.x packs blocks_per_ntt (= n / K_VALS =
  // 1 << (log_n - LOG_K)) chunks per NTT, then cosets in tile, then columns.
  // Input is shared across cosets (same monomial source); output is
  // coset-major with per-coset stride = `num_cols_per_coset` columns.
  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - LOG_K;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  gmem_in.add_col(fi.col);
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const int coset_factor_power = (coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift;

  const unsigned chunk_idx = fi.intra_x;
  const int gmem_block_offset = static_cast<int>(chunk_idx) << LOG_K;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  extern __shared__ bf smem[];

  if (coset_factor_power > 0) {
    for (int gid = threadIdx.x; gid < K_VALS; gid += COMPACT_THREADS) {
      bf value = gmem_in.get_at_row(gid);
      const unsigned global_bitrev_idx = static_cast<unsigned>(gmem_block_offset) + static_cast<unsigned>(gid);
      const unsigned natural_idx = bitrev(global_bitrev_idx, log_n);
      const bf coset_offset = get_power_from_layers(::ab_ntt_forward_powers, natural_idx * static_cast<unsigned>(coset_factor_power));
      value = bf::mul(value, coset_offset);
      smem[gid] = value;
    }
  } else {
    for (int gid = threadIdx.x; gid < K_VALS; gid += COMPACT_THREADS) {
      smem[gid] = gmem_in.get_at_row(gid);
    }
  }
  __syncthreads();

#pragma unroll
  for (int stage = 0; stage < LOG_K; stage++) {
    const int pairs_per_group = 1 << stage;
    const int pairs_per_group_mask = pairs_per_group - 1;
    for (int gid_local = threadIdx.x; gid_local < HALF_K; gid_local += COMPACT_THREADS) {
      const int group_local = gid_local >> stage;
      const int pair = gid_local & pairs_per_group_mask;
      const int left_idx = (group_local << (stage + 1)) + pair;
      const int right_idx = left_idx + pairs_per_group;
      bf left = smem[left_idx];
      bf right = smem[right_idx];
      bf twiddled_diff = bf::sub(left, right);
      // Global group index for this butterfly in the size-2^log_n NTT.
      const unsigned group_global = (chunk_idx << (LOG_K - 1 - stage)) + static_cast<unsigned>(group_local);
      const unsigned twiddle_power = bitrev(group_global, log_n - 1) << (OMEGA_LOG_ORDER - log_n);
      twiddled_diff = bf::mul(twiddled_diff, get_forward_twiddle_power(twiddle_power));
      smem[left_idx] = bf::add(left, right);
      smem[right_idx] = twiddled_diff;
    }
    __syncthreads();
  }

  for (int idx = threadIdx.x; idx < K_VALS; idx += COMPACT_THREADS) {
    gmem_out.set_at_row(idx, smem[idx]);
  }
}

#define DEFINE_FIRST_K_KERNEL(LOG_K, MIN_BLOCKS_PER_SM)                                                                                                        \
  EXTERN __launch_bounds__(COMPACT_THREADS, MIN_BLOCKS_PER_SM)                                                                                                 \
  __global__ void ab_monomials_to_evals_first_##LOG_K##_stages_compact_kernel(                                                                                 \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const bool transposed_monomials, const int log_n,                 \
      const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {                                  \
    (void)transposed_monomials;                                                                                                                                \
    monomials_to_evals_first_stages_in_block<LOG_K>(gmem_in, gmem_out, log_n, coset_index_base, coset_factor_shift, num_cols_per_coset, log_cosets_in_tile);   \
  }

// 2 blocks/SM at all chunk sizes: K=12 needs 16 KB smem per block, well below
// the static cap. K=5, 6 are included so the 2-pass-compact-initial path can
// cover log_n=13, 14 -- where the single-block compact-1-pass design starves
// the SMs.
DEFINE_FIRST_K_KERNEL(5, 2)
DEFINE_FIRST_K_KERNEL(6, 2)
DEFINE_FIRST_K_KERNEL(7, 2)
DEFINE_FIRST_K_KERNEL(8, 2)
DEFINE_FIRST_K_KERNEL(9, 2)
DEFINE_FIRST_K_KERNEL(10, 2)
DEFINE_FIRST_K_KERNEL(11, 2)
DEFINE_FIRST_K_KERNEL(12, 2)

#undef DEFINE_FIRST_K_KERNEL

} // namespace airbender::ntt
