#include "ntt.cuh"

namespace airbender::ntt {

// Compact-range hypercube tail for log_n in [13, 20]. The preceding
// nonfinal8 pass owns bits log_n-1 .. log_n-8; each block here owns one
// consecutive 2^LOG_K-row chunk and applies the remaining bits LOG_K-1 .. 0.
// There are exactly 2^8 disjoint chunks for LOG_K = log_n - 8. The family
// uses LOG_K=5..11; log_n=20 keeps the faster 8+8+4 three-pass shape.
constexpr int HYPERCUBE_COMPACT_THREADS = 256;

template <int LOG_K>
DEVICE_FORCEINLINE void hypercube_evals_to_monomials_last_stages_compact(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                                                         bf_matrix_setter<st_modifier::cg> gmem_out) {
  static_assert(LOG_K >= 5 && LOG_K <= 11);
  constexpr int K_VALS = 1 << LOG_K;
  constexpr int HALF_K = K_VALS >> 1;

  const int gmem_block_offset = static_cast<int>(blockIdx.x) << LOG_K;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  extern __shared__ bf smem[];

  for (int idx = threadIdx.x; idx < K_VALS; idx += HYPERCUBE_COMPACT_THREADS)
    smem[idx] = gmem_in.get_at_row(idx);
  __syncthreads();

#pragma unroll
  for (int stage = 0; stage < LOG_K; stage++) {
    const int log_distance = LOG_K - 1 - stage;
    const int distance = 1 << log_distance;
    for (int gid = threadIdx.x; gid < HALF_K; gid += HYPERCUBE_COMPACT_THREADS) {
      const int region = gid >> log_distance;
      const int pair = gid & (distance - 1);
      const int left_idx = (region << (log_distance + 1)) + pair;
      const int right_idx = left_idx + distance;
      smem[right_idx] = bf::sub(smem[right_idx], smem[left_idx]);
    }
    __syncthreads();
  }

  for (int idx = threadIdx.x; idx < K_VALS; idx += HYPERCUBE_COMPACT_THREADS)
    gmem_out.set_at_row(idx, smem[idx]);
}

#define DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(LOG_K)                                                                                                            \
  EXTERN __launch_bounds__(HYPERCUBE_COMPACT_THREADS, 2) __global__ void ab_hypercube_evals_to_monomials_last_##LOG_K##_stages_compact_kernel(                 \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out) {                                                                 \
    hypercube_evals_to_monomials_last_stages_compact<LOG_K>(gmem_in, gmem_out);                                                                                \
  }

DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(5)
DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(6)
DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(7)
DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(8)
DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(9)
DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(10)
DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL(11)

#undef DEFINE_HYPERCUBE_LAST_COMPACT_KERNEL

} // namespace airbender::ntt
