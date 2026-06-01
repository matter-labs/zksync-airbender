#include "ntt.cuh"

// Smem-packed multi-NTT-per-block monomials -> natural evals NTT.
//
// Pack `1 << LOG_INSTANCES_PER_BLOCK` independent NTT instances of size
// `1 << LOG_N` into a single block, with each instance assigned exactly
// `HALF_N = 1 << (LOG_N - 1)` threads (one thread per butterfly per stage).
// Block thread count = (HALF_N << LOG_INSTANCES_PER_BLOCK); for the supported
// `LOG_N in [6, 8]` and `LOG_IPB` chosen so HALF_N * IPB <= 256, the block is
// fully utilized in every butterfly stage.
//
// Motivation: the compact 1-pass kernel uses 256 threads/block regardless of
// log_n. At log_n=6/7/8 only 32/64/128 threads do butterfly work, leaving
// 87.5/75/50% of block threads idle. SM occupancy is capped by the per-block
// thread count, so each underutilized block effectively wastes SM throughput.
// Packing IPB = 8/4/2 NTT instances per block restores full utilization at the
// log_n range where the compact kernel runs (recursive WHIR + small folds).
//
// Smem layout: instance `i` lives at `smem[i * N .. (i + 1) * N]` (coset-major
// inside the block). `__syncthreads()` after each butterfly stage synchronizes
// all instances together -- safe because every instance is at the same stage.

namespace airbender::ntt {

template <int LOG_N, int LOG_INSTANCES_PER_BLOCK>
DEVICE_FORCEINLINE void monomials_to_evals_smem_packed_impl(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                            const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset,
                                                            const int log_cosets_in_tile) {
  constexpr int N = 1 << LOG_N;
  constexpr int HALF_N = N >> 1;
  constexpr int INSTANCES_PER_BLOCK = 1 << LOG_INSTANCES_PER_BLOCK;
  constexpr int THREADS_PER_INSTANCE = HALF_N;
  constexpr int BLOCK_THREADS = THREADS_PER_INSTANCE * INSTANCES_PER_BLOCK;
  static_assert(BLOCK_THREADS <= 256, "smem-packed block must fit 256 threads");

  const int local_instance = threadIdx.x >> (LOG_N - 1);
  const int local_gid = threadIdx.x & (HALF_N - 1);

  // Each block holds IPB consecutive flat-instance indices. The flat index
  // packs (col, coset_in_tile) the same way `decompose_flat_2d` does for the
  // compact 1-pass kernel: coset_in_tile in the low bits, col in the high
  // bits. Intra-block ordering: local_instance is the low LOG_IPB bits of the
  // flat index, so threads inside a block march across cosets (then cols)
  // together.
  const unsigned flat_instance = (blockIdx.x << LOG_INSTANCES_PER_BLOCK) | static_cast<unsigned>(local_instance);
  const unsigned coset_in_tile = flat_instance & ((1u << log_cosets_in_tile) - 1u);
  const unsigned col = flat_instance >> log_cosets_in_tile;

  gmem_in.add_col(static_cast<int>(col));
  gmem_out.add_col(static_cast<int>(coset_in_tile) * num_cols_per_coset + static_cast<int>(col));
  const int coset_factor_power = (coset_index_base + static_cast<int>(coset_in_tile)) << coset_factor_shift;

  extern __shared__ bf smem_all[];
  bf *smem = smem_all + local_instance * N;

  // Load: each thread reads two elements (gid = local_gid and local_gid + HALF_N)
  // because THREADS_PER_INSTANCE = HALF_N covers exactly half of N. Coset shift
  // (when coset_factor_power > 0) multiplies each natural-index coefficient by
  // tau^(coset_factor_power * natural_idx).
  if (coset_factor_power > 0) {
#pragma unroll
    for (int slot = 0; slot < 2; slot++) {
      const int gid = local_gid + slot * HALF_N;
      bf value = gmem_in.get_at_row(gid);
      const unsigned natural_idx = bitrev(static_cast<unsigned>(gid), LOG_N);
      const bf coset_offset = get_power_from_layers(::ab_ntt_forward_powers, natural_idx * static_cast<unsigned>(coset_factor_power));
      smem[gid] = bf::mul(value, coset_offset);
    }
  } else {
#pragma unroll
    for (int slot = 0; slot < 2; slot++) {
      const int gid = local_gid + slot * HALF_N;
      smem[gid] = gmem_in.get_at_row(gid);
    }
  }
  __syncthreads();

  // Butterflies: one butterfly per thread per stage. THREADS_PER_INSTANCE =
  // HALF_N so `local_gid` directly indexes the butterfly within the instance.
  // Indexing mirrors `monomials_to_evals_all_stages_in_block` in
  // monomials_to_evals_compact.cu.
#pragma unroll
  for (int stage = 0; stage < LOG_N; stage++) {
    const int pairs_per_group = 1 << stage;
    const int pairs_per_group_mask = pairs_per_group - 1;
    const int group = local_gid >> stage;
    const int pair = local_gid & pairs_per_group_mask;
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
    __syncthreads();
  }

  // Store: two elements per thread to match the load.
#pragma unroll
  for (int slot = 0; slot < 2; slot++) {
    const int gid = local_gid + slot * HALF_N;
    gmem_out.set_at_row(gid, smem[gid]);
  }
}

// MIN_BLOCKS_PER_SM = 4: each block uses BLOCK_THREADS = 256 threads and
// smem = N * IPB * sizeof(bf) = 2 KB for all (LOG_N, IPB) combinations below,
// so 4 blocks/SM is comfortable on every supported architecture.
#define DEFINE_SMEM_PACKED_KERNEL(LOG_N, LOG_IPB)                                                                                                              \
  EXTERN __launch_bounds__((1 << (LOG_N - 1)) << LOG_IPB, 4) __global__ void ab_monomials_to_evals_smem_packed_##LOG_N##_stages_ipb##LOG_IPB##_kernel(         \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const bool transposed_monomials, const int log_n,                 \
      const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {                                  \
    (void)transposed_monomials;                                                                                                                                \
    (void)log_n;                                                                                                                                               \
    monomials_to_evals_smem_packed_impl<LOG_N, LOG_IPB>(gmem_in, gmem_out, coset_index_base, coset_factor_shift, num_cols_per_coset, log_cosets_in_tile);      \
  }

// (LOG_N, LOG_IPB) covers the underutilized compact range:
//   LOG_N=6: HALF_N=32, IPB=8  -> 256 threads, 2 KB smem
//   LOG_N=7: HALF_N=64, IPB=4  -> 256 threads, 2 KB smem
//   LOG_N=8: HALF_N=128, IPB=2 -> 256 threads, 2 KB smem
// LOG_N >= 9 already uses all 256 threads in the compact 1-pass kernel, so no
// packing helps.
DEFINE_SMEM_PACKED_KERNEL(6, 3)
DEFINE_SMEM_PACKED_KERNEL(7, 2)
DEFINE_SMEM_PACKED_KERNEL(8, 1)

#undef DEFINE_SMEM_PACKED_KERNEL

} // namespace airbender::ntt
