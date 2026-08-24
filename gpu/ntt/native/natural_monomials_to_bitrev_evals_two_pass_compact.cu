#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

// Natural-order monomials -> bitreversed-order evaluations, two-pass-compact
// regime (log_n in [13, 20]): out_k[p] = f(g_k * omega^rev_n(p)).
//
// Pass 1 is the three-pass initial kernel (stages 0..7 over decimated exchange
// groups, coset pre-scale, multi-coset fan-out) -- it is already log_n-generic
// down to 13. This TU holds pass 2: the remaining K = log_n - 8 stages, whose
// exchange regions are chunks of 2^K CONSECUTIVE rows, one chunk per block, in
// place per coset slab.
//
// It is the mirror image of the forward plan's `first_K_stages_compact` pass:
// the forward network's consecutive-chunk end is its FIRST K stages, the
// descending-stride network's is its LAST K stages. The stage recipe follows
// `serial_ct_ntt_natural_to_bitreversed`: descending distance, one twiddle per
// contiguous exchange region, `(a + t*b, a - t*b)`, with the region twiddle
// read at the bitreversed global region index.

constexpr int LAST_COMPACT_THREADS = 256;

template <int LOG_K>
DEVICE_FORCEINLINE void natural_monomials_to_bitrev_evals_last_stages_in_block(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                                                               bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,
                                                                               const int num_cols_per_coset, const int log_cosets_in_tile) {
  constexpr int K_VALS = 1 << LOG_K;
  constexpr int HALF_K = K_VALS >> 1;

  // Flat-blockIdx.x layout: gridDim.x packs blocks_per_ntt (= n / K_VALS =
  // 1 << (log_n - LOG_K)) chunks per NTT, then cosets in tile, then columns.
  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - LOG_K;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  apply_flat_col_offset(fi, num_cols_per_coset, gmem_in, gmem_out);

  const unsigned chunk_idx = fi.intra_x;
  const int gmem_block_offset = static_cast<int>(chunk_idx) << LOG_K;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  extern __shared__ bf smem[];

  for (int gid = threadIdx.x; gid < K_VALS; gid += LAST_COMPACT_THREADS)
    smem[gid] = gmem_in.get_at_row(gid);
  __syncthreads();

  // Local stage `s` is global stage `log_n - LOG_K + s`: the chunk holds 2^s
  // exchange regions of 2^(LOG_K - s) rows, butterfly distance
  // 2^(LOG_K - 1 - s).
#pragma unroll
  for (int s = 0; s < LOG_K; s++) {
    const int log_distance = LOG_K - 1 - s;
    const int distance = 1 << log_distance;
    for (int gid = threadIdx.x; gid < HALF_K; gid += LAST_COMPACT_THREADS) {
      const int region_local = gid >> log_distance;
      const int pair = gid & (distance - 1);
      const int left_idx = (region_local << (log_distance + 1)) + pair;
      const int right_idx = left_idx + distance;
      const unsigned region_global = (chunk_idx << s) + static_cast<unsigned>(region_local);
      const unsigned twiddle_power = bitrev(region_global, static_cast<unsigned>(log_n - 1)) << (OMEGA_LOG_ORDER - log_n);
      const bf left = smem[left_idx];
      const bf right = bf::mul(smem[right_idx], get_forward_twiddle_power(twiddle_power));
      smem[left_idx] = bf::add(left, right);
      smem[right_idx] = bf::sub(left, right);
    }
    __syncthreads();
  }

  for (int idx = threadIdx.x; idx < K_VALS; idx += LAST_COMPACT_THREADS)
    gmem_out.set_at_row(idx, smem[idx]);
}

// Shares the NaturalToBitrevFinal signature: pass 2 needs no coset arguments
// (it runs in place on a coset slab) and no `transposed_monomials` (the
// bitreversed codeword is always written in plain row order).
#define DEFINE_LAST_K_KERNEL(LOG_K, MIN_BLOCKS_PER_SM)                                                                                                         \
  EXTERN __launch_bounds__(LAST_COMPACT_THREADS, MIN_BLOCKS_PER_SM)                                                                                            \
  __global__ void ab_natural_monomials_to_bitrev_evals_last_##LOG_K##_stages_compact_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in,                         \
                                                                                            bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n,       \
                                                                                            const int num_cols_per_coset, const int log_cosets_in_tile) {      \
    natural_monomials_to_bitrev_evals_last_stages_in_block<LOG_K>(gmem_in, gmem_out, log_n, num_cols_per_coset, log_cosets_in_tile);                           \
  }

// 2 blocks/SM at all chunk sizes: LOG_K = 12 needs 16 KB dynamic smem.
DEFINE_LAST_K_KERNEL(5, 2)
DEFINE_LAST_K_KERNEL(6, 2)
DEFINE_LAST_K_KERNEL(7, 2)
DEFINE_LAST_K_KERNEL(8, 2)
DEFINE_LAST_K_KERNEL(9, 2)
DEFINE_LAST_K_KERNEL(10, 2)
DEFINE_LAST_K_KERNEL(11, 2)
DEFINE_LAST_K_KERNEL(12, 2)

#undef DEFINE_LAST_K_KERNEL

} // namespace airbender::ntt
