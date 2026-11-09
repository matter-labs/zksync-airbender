#include "transform.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_5_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<5, false, lazy_dit_policy>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

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
    void ab_pr_dit_nonfinal_6_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<6, false, lazy_dit_policy>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_7_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<7, false, lazy_dit_policy>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<8, false, lazy_dit_policy>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(64, 16) __global__
    void ab_pr_dit_final_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                         const u32 log_n, const u32 start_stage, const chunk_map) {
  final<6, 8, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(256, 4) __global__
    void ab_pr_dit_final_10_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                          const u32 log_n, const u32 start_stage, const chunk_map) {
  final<8, 10, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__
    void ab_pr_dit_final_12_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                          const u32 log_n, const u32 start_stage, const chunk_map) {
  final<10, 12, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__
    void ab_pr_dit_small_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                const u32 log_n, const u32 start_stage, const chunk_map) {
  small<dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_5_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<5, false, lazy_dit_policy, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_6_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<6, false, lazy_dit_policy, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_dit_nonfinal_7_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<7, false, lazy_dit_policy, true>(in, out, lazy_dit_policy{{d}}, log_n, start_stage, map, scale);
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

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_6_1_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<6, 1>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_6_2_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<6, 2>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_6_3_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<6, 3>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_6_4_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<6, 4>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_1_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 1>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_2_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 2>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_3_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 3>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_7_4_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<7, 4>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_1_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 1>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_2_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 2>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_3_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 3>(lazy_dit_policy{{d}}, args);
}

EXTERN __launch_bounds__(256, 2) __global__ void ab_pr_dit_suffix_micro_8_4_kernel(const suffix_tile_args args, const proth120_twiddle_descriptor d) {
  suffix_micro<8, 4>(lazy_dit_policy{{d}}, args);
}

} // namespace airbender::ntt
