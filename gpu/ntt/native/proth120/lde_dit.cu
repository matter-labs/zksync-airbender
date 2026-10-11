#include "transform.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_5_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage) {
  nonfinal<5, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_6_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage) {
  nonfinal<6, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_7_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage) {
  nonfinal<7, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_dit_nonfinal_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                            const u32 log_n, const u32 start_stage) {
  nonfinal<8, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(64, 16) __global__ void ab_pr_dit_final_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                                                 const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage) {
  final<6, 8, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(256, 4) __global__ void ab_pr_dit_final_10_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                                                  const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage) {
  final<8, 10, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__
    void ab_pr_dit_final_12_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const proth120_twiddle_descriptor d,
                                          const u32 log_n, const u32 start_stage) {
  final<10, 12, dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__ void ab_pr_dit_small_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                                         const proth120_twiddle_descriptor d, const u32 log_n, const u32 start_stage) {
  small<dit_policy>(in, out, dit_policy{d}, log_n, start_stage);
}

} // namespace airbender::ntt
