// Feature-only Boolean-X1 sharing, with unchanged fold and selector geometry.
#include "fused_executor.cuh"

namespace airbender::gkr::backward {

AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_x1_reference_00_dynamic, 0x00, 2, false, true, 48, 1024, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_x1_reference_01_dynamic, 0x01, 2, false, true, 48, 1024, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_x1_reference_03_dynamic, 0x03, 2, false, true, 48, 1024, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_x1_reference_07_dynamic, 0x07, 2, false, true, 48, 1024, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_x1_reference_13_dynamic, 0x13, 2, false, true, 48, 1024, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_x1_reference_17_dynamic, 0x17, 2, false, true, 48, 1024, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_x1_reference_1f_dynamic, 0x1f, 2, false, true, 48, 1024, true, false);

template <u16 Shape, u32 X1, bool StaticX0> DEVICE_FORCEINLINE void bwd_main_cont_x1_split_dispatch(const bwd_main_cont_window_desc &desc) {
  if constexpr (StaticX0)
    bwd_main_cont_window_dispatch_x0<Shape, X1, true, true>(desc);
  else
    bwd_main_cont_window_execute<Shape, X1, BWD_MAIN_CONT_WINDOW_DYNAMIC_X0, true>(desc);
}

#define AB_MAIN_X1_FUSED(Name, Shape, StaticX0)                                                                                                                \
  EXTERN __global__ __launch_bounds__(BWD_MAIN_CONT_FUSED_THREADS, 2) void Name(const __grid_constant__ bwd_main_cont_window_desc desc) {                      \
    if (blockDim.x != BWD_MAIN_CONT_FUSED_THREADS || gridDim.x != desc.row_tiles || desc.publication_fold != 3 ||                                              \
        desc.source_count > BWD_MAIN_CONT_WINDOW_MAX_SOURCES || desc.fold_list_offsets[BWD_MAIN_CONT_WINDOW_WARPS] != desc.source_count ||                     \
        desc.program_words > BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP || desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM != 0)                               \
      return;                                                                                                                                                  \
    bwd_main_cont_fused_execute<Shape, StaticX0, true, (StaticX0 ? 0 : 48), 1024, true, StaticX0, true>(desc);                                                 \
  }

#define AB_MAIN_X1_SPLIT(Name, Shape, StaticX0)                                                                                                                \
  EXTERN __global__ __launch_bounds__(BWD_MAIN_CONT_WINDOW_BLOCK_THREADS, 4) void Name(const __grid_constant__ bwd_main_cont_window_desc desc) {               \
    if (blockDim.x != BWD_MAIN_CONT_WINDOW_BLOCK_THREADS || gridDim.x != desc.row_tiles * BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS)                                \
      return;                                                                                                                                                  \
    if ((desc.publication_fold != 0 && desc.publication_fold != 3) || desc.source_count > BWD_MAIN_CONT_WINDOW_MAX_SOURCES ||                                  \
        desc.fold_list_offsets[BWD_MAIN_CONT_WINDOW_WARPS] != desc.source_count || desc.program_words > BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP ||               \
        desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM != 0)                                                                                             \
      return;                                                                                                                                                  \
    if (blockIdx.x % BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS < 2)                                                                                                 \
      bwd_main_cont_x1_split_dispatch<Shape, BWD_MAIN_CONT_WINDOW_BOOLEAN_X1, StaticX0>(desc);                                                                 \
    else                                                                                                                                                       \
      bwd_main_cont_x1_split_dispatch<Shape, 2, StaticX0>(desc);                                                                                               \
  }

AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_00_dynamic, 0x00, false);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_00_dynamic, 0x00, false);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_00_static, 0x00, true);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_00_static, 0x00, true);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_01_dynamic, 0x01, false);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_01_dynamic, 0x01, false);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_01_static, 0x01, true);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_01_static, 0x01, true);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_03_dynamic, 0x03, false);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_03_dynamic, 0x03, false);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_03_static, 0x03, true);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_03_static, 0x03, true);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_07_dynamic, 0x07, false);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_07_dynamic, 0x07, false);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_07_static, 0x07, true);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_07_static, 0x07, true);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_13_dynamic, 0x13, false);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_13_dynamic, 0x13, false);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_13_static, 0x13, true);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_13_static, 0x13, true);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_17_dynamic, 0x17, false);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_17_dynamic, 0x17, false);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_17_static, 0x17, true);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_17_static, 0x17, true);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_1f_dynamic, 0x1f, false);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_1f_dynamic, 0x1f, false);
AB_MAIN_X1_FUSED(ab_gkr_main_cont_x1_fused_1f_static, 0x1f, true);
AB_MAIN_X1_SPLIT(ab_gkr_main_cont_x1_split_1f_static, 0x1f, true);

} // namespace airbender::gkr::backward
