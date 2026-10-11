#include "transform.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_mobius_nonfinal_5_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage) {
  nonfinal<5, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_mobius_nonfinal_6_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage) {
  nonfinal<6, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_mobius_nonfinal_7_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage) {
  nonfinal<7, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(512, 2) __global__
    void ab_pr_mobius_nonfinal_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage) {
  nonfinal<8, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(64, 16) __global__ void ab_pr_mobius_final_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                                                    const u32 log_n, const u32 start_stage) {
  final<6, 8, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(256, 4) __global__
    void ab_pr_mobius_final_10_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                             const u32 start_stage) {
  final<8, 10, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__
    void ab_pr_mobius_final_12_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                             const u32 start_stage) {
  final<10, 12, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__
    void ab_pr_mobius_small_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n, const u32 start_stage) {
  small<mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

} // namespace airbender::ntt
