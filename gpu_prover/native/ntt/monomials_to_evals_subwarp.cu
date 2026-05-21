#include "ntt.cuh"

// Sub-warp register-resident multi-NTT-per-block monomials -> natural evals NTT.
//
// For LOG_N in {4, 5}, one NTT instance fits within a single warp (LOG_N=5 =
// 32 lanes = 1 warp; LOG_N=4 = 16 lanes = 0.5 warp). Each thread holds exactly
// one element value in a register; the butterfly exchange uses
// `__shfl_xor_sync` to swap with the partner at `lane ^ (1 << stage)`. No smem,
// no `__syncthreads`.
//
// Smem-packed (variant D2) covers LOG_N in [6, 8] where the NTT outgrows one
// warp; sub-warp covers LOG_N in {4, 5} where the smaller working set lets us
// avoid the smem trip entirely. At LOG_N=4 two NTTs share a warp (lanes 0..15
// and 16..31); the XOR partner masks (1, 2, 4, 8) never flip bit 4, so the
// shfl stays within each sub-warp NTT.
//
// Block layout (all variants pack IPB instances per block to keep block_threads
// = 256, matching the compact kernel's SM thread budget):
//   LOG_N=4: THREADS_PER_INSTANCE=16,  INSTANCES_PER_BLOCK=16 -> 256 threads
//   LOG_N=5: THREADS_PER_INSTANCE=32,  INSTANCES_PER_BLOCK=8  -> 256 threads
// Flat instance index packs (col, coset_in_tile) the same way the smem-packed
// kernel does; intra-block ordering puts cosets innermost.

namespace airbender::ntt {

template <int LOG_N, int LOG_INSTANCES_PER_BLOCK>
DEVICE_FORCEINLINE void monomials_to_evals_subwarp_impl(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                        const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset,
                                                        const int log_cosets_in_tile) {
  constexpr int N = 1 << LOG_N;
  constexpr int INSTANCES_PER_BLOCK = 1 << LOG_INSTANCES_PER_BLOCK;
  constexpr int THREADS_PER_INSTANCE = N; // one thread per element
  constexpr int BLOCK_THREADS = THREADS_PER_INSTANCE * INSTANCES_PER_BLOCK;
  static_assert(BLOCK_THREADS <= 256, "subwarp block must fit 256 threads");
  static_assert(LOG_N <= 5, "subwarp NTT requires the instance to fit within a warp");
  // __shfl_xor_sync needs the mask to match the active lanes in the warp.
  // For BLOCK_THREADS < 32 (the IPB=1 variants at LOG_N < 5) the upper lanes
  // are inactive; passing the wider mask would be undefined behavior.
  constexpr unsigned WARP_MASK = (BLOCK_THREADS < 32) ? ((1u << BLOCK_THREADS) - 1u) : 0xffffffffu;

  const int local_instance = threadIdx.x >> LOG_N;
  const int lane_in_ntt = threadIdx.x & (N - 1);

  const unsigned flat_instance = (blockIdx.x << LOG_INSTANCES_PER_BLOCK) | static_cast<unsigned>(local_instance);
  const unsigned coset_in_tile = flat_instance & ((1u << log_cosets_in_tile) - 1u);
  const unsigned col = flat_instance >> log_cosets_in_tile;

  gmem_in.add_col(static_cast<int>(col));
  gmem_out.add_col(static_cast<int>(coset_in_tile) * num_cols_per_coset + static_cast<int>(col));
  const int coset_factor_power = (coset_index_base + static_cast<int>(coset_in_tile)) << coset_factor_shift;

  // Load: each thread reads its single bitreversed-input element and (when
  // coset_factor_power > 0) folds in the coset shift
  // (tau^(natural_idx * coset_factor_power)).
  bf v = gmem_in.get_at_row(lane_in_ntt);
  if (coset_factor_power > 0) {
    const unsigned natural_idx = bitrev(static_cast<unsigned>(lane_in_ntt), LOG_N);
    const bf coset_offset = get_power_from_layers(::ab_ntt_forward_powers, natural_idx * static_cast<unsigned>(coset_factor_power));
    v = bf::mul(v, coset_offset);
  }

  // Butterflies via __shfl_xor_sync: at stage s, partner = lane XOR (1 << s).
  // The thread with bit s clear ("left") keeps the sum; the thread with bit s
  // set ("right") keeps the twiddled diff. Same correspondence as the smem
  // kernels: pair_idx (sometimes "gid" in compact) = lane_in_ntt with bit s
  // masked out, so group = lane_in_ntt >> (s + 1).
  //
  // bf is a 32-bit BabyBear field element; __shfl_xor_sync on a 32-bit lane
  // value is a single SHFL instruction. Values held in registers between
  // stages are always reduced (`bf::add`/`bf::sub`/`bf::mul` all reduce on
  // exit), so `from_reduced_raw_repr` is safe on the shfl result.
#pragma unroll
  for (int stage = 0; stage < LOG_N; stage++) {
    const unsigned partner_mask = 1u << stage;
    const unsigned partner_bits = __shfl_xor_sync(WARP_MASK, bf::into_raw_u32(v), static_cast<int>(partner_mask));
    const bf partner = bf::from_reduced_raw_repr(partner_bits);
    const bool is_left = (static_cast<unsigned>(lane_in_ntt) & partner_mask) == 0u;
    const bf left = is_left ? v : partner;
    const bf right = is_left ? partner : v;
    bf sum = bf::add(left, right);
    bf diff = bf::sub(left, right);
    if (stage + 1 < LOG_N) {
      const unsigned group = static_cast<unsigned>(lane_in_ntt) >> (stage + 1);
      const unsigned twiddle_power = bitrev(group, LOG_N - 1) << (OMEGA_LOG_ORDER - LOG_N);
      diff = bf::mul(diff, get_forward_twiddle_power(twiddle_power));
    }
    v = is_left ? sum : diff;
  }

  gmem_out.set_at_row(lane_in_ntt, v);
}

// MIN_BLOCKS_PER_SM = 4: each block uses 256 threads and 0 smem, so 4 blocks
// per SM is a safe occupancy target on every supported architecture.
#define DEFINE_SUBWARP_KERNEL(LOG_N, LOG_IPB)                                                                                                                  \
  EXTERN __launch_bounds__((1 << LOG_N) << LOG_IPB, 4) __global__ void ab_monomials_to_evals_subwarp_##LOG_N##_stages_ipb##LOG_IPB##_kernel(                   \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const bool transposed_monomials, const int log_n,                 \
      const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {                                  \
    (void)transposed_monomials;                                                                                                                                \
    (void)log_n;                                                                                                                                               \
    monomials_to_evals_subwarp_impl<LOG_N, LOG_IPB>(gmem_in, gmem_out, coset_index_base, coset_factor_shift, num_cols_per_coset, log_cosets_in_tile);          \
  }

// (LOG_N, LOG_IPB) covers the sub-warp range with block_threads = 256:
//   LOG_N=1: THREADS_PER_INSTANCE=2,  IPB=128 -> 256 threads
//   LOG_N=2: THREADS_PER_INSTANCE=4,  IPB=64  -> 256 threads
//   LOG_N=3: THREADS_PER_INSTANCE=8,  IPB=32  -> 256 threads
//   LOG_N=4: THREADS_PER_INSTANCE=16, IPB=16  -> 256 threads
//   LOG_N=5: THREADS_PER_INSTANCE=32, IPB=8   -> 256 threads
// Below LOG_N=4 the per-stage fallback (`bitreversed_coeffs_to_natural_coset`
// in `mod.rs`) used to issue `log_n + 1` separate kernel launches per NTT;
// the sub-warp variant collapses that to a single launch.
DEFINE_SUBWARP_KERNEL(1, 7)
DEFINE_SUBWARP_KERNEL(2, 6)
DEFINE_SUBWARP_KERNEL(3, 5)
DEFINE_SUBWARP_KERNEL(4, 4)
DEFINE_SUBWARP_KERNEL(5, 3)
// IPB=1 variants for LOG_N in [1, 3]: the strategy picks these when the
// per-launch workload (num_cosets * num_columns) is below IPB_max, so we don't
// need a smem-packed / compact 1-pass fallback for that range. BLOCK_THREADS
// = N = {2, 4, 8} -- the warp mask narrows accordingly via WARP_MASK above.
DEFINE_SUBWARP_KERNEL(1, 0)
DEFINE_SUBWARP_KERNEL(2, 0)
DEFINE_SUBWARP_KERNEL(3, 0)

#undef DEFINE_SUBWARP_KERNEL

} // namespace airbender::ntt
