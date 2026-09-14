#include "fused_executor.cuh"

namespace airbender::gkr::backward {

// Diagnostic-only: preserve the original full-program selector strategy.
// The dense source table is complete; only the first-owner fold list is partial.
#define PARTITION_ENTRY(Name, StaticX0)                                                                                                                        \
  EXTERN __global__ __launch_bounds__(288, 2) void Name(const __grid_constant__ bwd_main_cont_window_desc desc, const u32 fold_count) {                        \
    if (blockDim.x != 288 || gridDim.x != desc.row_tiles || desc.publication_fold != 3 || desc.source_count > BWD_MAIN_CONT_WINDOW_MAX_SOURCES ||              \
        fold_count > desc.source_count || desc.fold_list_offsets[9] != fold_count || desc.program_words > BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP ||             \
        desc.program_words % 3 != 0)                                                                                                                           \
      return;                                                                                                                                                  \
    bwd_main_cont_fused_execute<0x1f, StaticX0, true, (StaticX0 ? 0 : 48), 1024, true, StaticX0, true, false>(desc);                                           \
  }
PARTITION_ENTRY(ab_gkr_main_cont_partition_dynamic, false)
PARTITION_ENTRY(ab_gkr_main_cont_partition_static, true)
#undef PARTITION_ENTRY

#define PAIRED_PARTITION_ENTRY(Name, StaticX0)                                                                                                                 \
  EXTERN __global__ __launch_bounds__(288, 2) void Name(const __grid_constant__ bwd_main_cont_window_desc desc, const u32 fold_count) {                        \
    if (blockDim.x != 288 || gridDim.x != desc.row_tiles || desc.publication_fold != 3 || desc.source_count > BWD_MAIN_CONT_WINDOW_MAX_SOURCES ||              \
        fold_count > desc.source_count || desc.fold_list_offsets[9] != fold_count || desc.program_words > BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP ||             \
        desc.program_words % 3 != 0)                                                                                                                           \
      return;                                                                                                                                                  \
    bwd_main_cont_fused_execute<0x1f, StaticX0, true, (StaticX0 ? 0 : 48), 1024, true, StaticX0, true, true>(desc);                                            \
  }
PAIRED_PARTITION_ENTRY(ab_gkr_main_cont_partition_paired, false)
#undef PAIRED_PARTITION_ENTRY

// Check every original tile/cell, including a census of all candidate cells.
EXTERN __global__ void ab_gkr_main_cont_partition_check(const e4 *expected, const e4 *parts, const u32 cells, const u32 partitions, u32 *status) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= cells)
    return;
  e4 sum = parts[i];
  u32 flags = 0;
  for (u32 p = 0; p < partitions; ++p) {
    const e4 value = parts[p * cells + i];
    const u32 *limbs = reinterpret_cast<const u32 *>(&value);
#pragma unroll
    for (u32 j = 0; j < 4; ++j)
      if (limbs[j] == 0xa5a5a5a5u)
        flags |= 2;
    if (p)
      sum = e4::add(sum, value);
  }
  const u32 *actual = reinterpret_cast<const u32 *>(&sum);
  const u32 *reference = reinterpret_cast<const u32 *>(&expected[i]);
#pragma unroll
  for (u32 j = 0; j < 4; ++j)
    if (actual[j] != reference[j])
      flags |= 1;
  if (flags)
    atomicOr(status, flags);
}
} // namespace airbender::gkr::backward
