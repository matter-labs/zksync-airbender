#include "transform.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(64, 20) __global__
    void ab_pr_dit_nonfinal_5_stages_narrow_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<5, true, lazy_dit_policy, false, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(128, 10) __global__
    void ab_pr_dit_nonfinal_6_stages_narrow_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<6, true, lazy_dit_policy, false, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(256, 5) __global__
    void ab_pr_dit_nonfinal_7_stages_narrow_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<7, true, lazy_dit_policy, false, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<8, false, lazy_dit_policy>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_8_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<8, false, lazy_dit_policy, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(64, 20) __global__
    void ab_pr_dit_nonfinal_5_stages_narrow_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                          const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                          const coset_scale scale) {
  nonfinal<5, true, lazy_dit_policy, true, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(128, 10) __global__
    void ab_pr_dit_nonfinal_6_stages_narrow_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                          const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                          const coset_scale scale) {
  nonfinal<6, true, lazy_dit_policy, true, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(256, 5) __global__
    void ab_pr_dit_nonfinal_7_stages_narrow_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                          const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                          const coset_scale scale) {
  nonfinal<7, true, lazy_dit_policy, true, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_1_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 1>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_1_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 1>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_4_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 4>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_5_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 5>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_2_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 2>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_3_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 3>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_2_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 2>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_3_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 3>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_6_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 6>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_4_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 4>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_5_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 5>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_6_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 6>(lazy_dit_policy{{d}}, args);
}

// Finish one-column, one-coset (R=8, V=1) tiles for parity tests and timing.
EXTERN __global__ void ab_pr_ntt_test_finish_pairs_kernel(pr *tiles, const proth120_twiddle_descriptor d, const u32 log_a, const u32 skip_bottom,
                                                          const u32 first_tile) {
  constexpr u32 LOG_F = 7;
  const u32 leaf = blockIdx.x * blockDim.x + threadIdx.x;
  const u32 w = leaf & ((1u << skip_bottom) - 1);
  const u32 f_lo = (leaf >> skip_bottom) & ((1u << LOG_F) - 1);
  const u32 tile = leaf >> (skip_bottom + LOG_F);
  const u32 g = ((first_tile + tile) << skip_bottom) + w;
  const u32 region = (bitreverse_low_bits(g, log_a) << LOG_F) | bitreverse_low_bits(f_lo, LOG_F);
  pr *pair = tiles + (static_cast<u64>(leaf) << 1);
  pr a = pair[0], b = pair[1];
  dit_policy{}.exchg(a, b, get_forward_pr_twiddle(d, region));
  pair[0] = a;
  pair[1] = b;
}

} // namespace airbender::ntt
