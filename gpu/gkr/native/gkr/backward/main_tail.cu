#include "main_tail.cuh"

EXTERN __global__ __launch_bounds__(airbender::gkr::backward::BWD_MAIN_TAIL_BLOCK_THREADS,
                                    1) void ab_gkr_bwd_main_tail_kernel(const __grid_constant__ airbender::gkr::backward::bwd_main_tail_desc desc) {
  using namespace airbender::gkr::backward;
  const u32 tail_rounds = u32{desc.folding_steps} - u32{desc.tail_start};
  if (blockDim.x != BWD_MAIN_TAIL_BLOCK_THREADS || gridDim.x != 1 || desc.k != BWD_MAIN_TAIL_K || desc.reserved != 0 ||
      desc.blob_bytes != BWD_MAIN_TAIL_BLOB_BYTES || desc.source_count == 0 || desc.source_count > BWD_MAIN_TAIL_SOURCE_CAP ||
      desc.program_words > BWD_MAIN_TAIL_PROGRAM_WORD_CAP || desc.program_words % airbender::gkr::BWD_SEG_WORDS_PER_TERM != 0 ||
      desc.immediate_count > BWD_MAIN_TAIL_IMMEDIATE_CAP || tail_rounds < 1 || tail_rounds > 6 || desc.entry_column_elems != (8u << tail_rounds) ||
      desc.eq_sizes.high[0] != 0 || desc.eq_sizes.high[1] != 0 || desc.eq_sizes.low != tail_rounds - 1 ||
      bwd_main_tail_list_offsets(desc)[BWD_MAIN_TAIL_K] != desc.program_words)
    return;
  bwd_main_tail_execute(desc);
}
