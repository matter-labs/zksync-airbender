#include "transform.cuh"

namespace airbender::ntt {

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_mobius_nonfinal_5_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage, const chunk_map map) {
  nonfinal<5, false, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_mobius_nonfinal_6_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage, const chunk_map map) {
  nonfinal<6, false, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_mobius_nonfinal_7_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage, const chunk_map map) {
  nonfinal<7, false, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(512, 3) __global__
    void ab_pr_mobius_nonfinal_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                               const u32 start_stage, const chunk_map map) {
  nonfinal<8, false, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage, map);
}

EXTERN __launch_bounds__(64, 16) __global__ void ab_pr_mobius_final_8_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                                                    const u32 log_n, const u32 start_stage, const chunk_map) {
  final<6, 8, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(256, 4) __global__
    void ab_pr_mobius_final_10_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                             const u32 start_stage, const chunk_map) {
  final<8, 10, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__
    void ab_pr_mobius_final_12_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, const u32 log_n,
                                             const u32 start_stage, const chunk_map) {
  final<10, 12, mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1) __global__ void ab_pr_mobius_small_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out,
                                                                            const u32 log_n, const u32 start_stage, const chunk_map) {
  small<mobius_policy>(in, out, mobius_policy{}, log_n, start_stage);
}

#define INVERSE_MOBIUS_NONFINAL(STAGES)                                                                                                                        \
  EXTERN __launch_bounds__(512, 3) __global__ void ab_pr_inverse_mobius_nonfinal_##STAGES##_stages_kernel(                                                     \
      pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, u32 log_n, u32 start_stage, chunk_map map) {                                \
    nonfinal<STAGES, false, inverse_mobius_policy>(in, out, inverse_mobius_policy{}, log_n, start_stage, map);                                                 \
  }

INVERSE_MOBIUS_NONFINAL(5)
INVERSE_MOBIUS_NONFINAL(6)
INVERSE_MOBIUS_NONFINAL(7)
INVERSE_MOBIUS_NONFINAL(8)
#undef INVERSE_MOBIUS_NONFINAL

#define INVERSE_MOBIUS_FINAL(STAGES, LOG_THREADS, BLOCKS_PER_SM)                                                                                               \
  EXTERN __launch_bounds__(1 << LOG_THREADS, BLOCKS_PER_SM)                                                                                                    \
  __global__ void ab_pr_inverse_mobius_final_##STAGES##_stages_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, u32 log_n,  \
                                                                      u32 start_stage, chunk_map) {                                                            \
    final<LOG_THREADS, STAGES, inverse_mobius_policy>(in, out, inverse_mobius_policy{}, log_n, start_stage);                                                   \
  }

INVERSE_MOBIUS_FINAL(8, 6, 16)
INVERSE_MOBIUS_FINAL(10, 8, 4)
INVERSE_MOBIUS_FINAL(12, 10, 1)
#undef INVERSE_MOBIUS_FINAL

EXTERN __launch_bounds__(1024, 1) __global__
    void ab_pr_inverse_mobius_small_kernel(pr_matrix_getter<ld_modifier::cg> in, pr_matrix_setter<st_modifier::cg> out, u32 log_n, u32 start_stage, chunk_map) {
  small<inverse_mobius_policy>(in, out, inverse_mobius_policy{}, log_n, start_stage);
}

} // namespace airbender::ntt
