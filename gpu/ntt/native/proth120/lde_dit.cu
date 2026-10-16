#include "transform.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_5_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<5, false, dit_policy>(in, out, dit_policy{d}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(64, 16) __global__
    void ab_pr_dit_nonfinal_5_stages_narrow_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<5, true, dit_policy>(in, out, dit_policy{d}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_pr_dit_nonfinal_6_stages_narrow_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<6, true, dit_policy>(in, out, dit_policy{d}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(256, 4) __global__
    void ab_pr_dit_nonfinal_7_stages_narrow_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<7, true, dit_policy>(in, out, dit_policy{d}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_6_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<6, false, dit_policy>(in, out, dit_policy{d}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_7_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<7, false, dit_policy>(in, out, dit_policy{d}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage, const chunk_map map) {
  nonfinal<8, false, dit_policy>(in, out, dit_policy{d}, log_n, start_stage, map);
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

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_5_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<5, false, dit_policy, true>(in, out, dit_policy{d}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_6_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<6, false, dit_policy, true>(in, out, dit_policy{d}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_7_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<7, false, dit_policy, true>(in, out, dit_policy{d}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_8_stages_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                   const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                   const coset_scale scale) {
  nonfinal<8, false, dit_policy, true>(in, out, dit_policy{d}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(64, 16) __global__
    void ab_pr_dit_nonfinal_5_stages_narrow_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                          const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                          const coset_scale scale) {
  nonfinal<5, true, dit_policy, true>(in, out, dit_policy{d}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_pr_dit_nonfinal_6_stages_narrow_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                          const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                          const coset_scale scale) {
  nonfinal<6, true, dit_policy, true>(in, out, dit_policy{d}, log_n, start_stage, map, scale);
}

EXTERN __launch_bounds__(256, 4) __global__
    void ab_pr_dit_nonfinal_7_stages_narrow_scaled_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                          const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage, const chunk_map map,
                                                          const coset_scale scale) {
  nonfinal<7, true, dit_policy, true>(in, out, dit_policy{d}, log_n, start_stage, map, scale);
}

} // namespace airbender::ntt
