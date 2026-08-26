#include "main_tail.cuh"

EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_TAIL_BLOCK_THREADS, 1) void ab_gkr_bwd_main_tail_kernel(
    const __grid_constant__ airbender::gkr::backward::bwd_main_tail_desc desc,
    const __grid_constant__ airbender::gkr::backward::bwd_main_tail_program_blob program_blob) {
  using namespace airbender::gkr::backward;
  bwd_main_tail_desc bound_desc = desc;
  bound_desc.program_blob = program_blob.bytes;
  const u32 tail_rounds = u32{bound_desc.folding_steps} - u32{bound_desc.tail_start};
  if (blockDim.x != BWD_MAIN_TAIL_BLOCK_THREADS || gridDim.x != 1 || bound_desc.source_count == 0 || bound_desc.source_count > BWD_MAIN_TAIL_SOURCE_CAP ||
      bound_desc.program_words > BWD_MAIN_TAIL_PROGRAM_WORD_CAP || bound_desc.program_words % airbender::gkr::BWD_CONTINUATION_WORDS_PER_TERM != 0 ||
      bound_desc.immediate_count > BWD_MAIN_TAIL_IMMEDIATE_CAP || tail_rounds < 1 || tail_rounds > 6 || bound_desc.entry_column_elems != (8u << tail_rounds) ||
      bound_desc.eq_sizes.high[0] != 0 || bound_desc.eq_sizes.high[1] != 0 || bound_desc.eq_sizes.low != tail_rounds - 1 ||
      bwd_main_tail_list_offsets(bound_desc)[BWD_MAIN_TAIL_K] != bound_desc.program_words)
    return;
  bwd_main_tail_execute(bound_desc);
}
