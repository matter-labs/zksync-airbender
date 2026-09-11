#pragma once

#include "../window/window_accumulator.cuh"
#include "fused_executor.cuh"

namespace airbender::gkr::backward {

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_output_wide(const bwd_main_cont_window_desc &desc, const bwd_main_cont_window_source_record &record,
                                                     const bwd_source_window &input_slot, const u32 output_index) {
  if (desc.publication_fold == 0) {
    // The zero-continuation chain needs the exact depth-zero source arena in
    // canonical E4 form. Base and virtual sources are embedded without a host
    // round trip; extension sources retain their original bytes.
    if (input_slot.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
      const gkr_base_source_kind kind = bwd_coeff_procedural_source_kind(input_slot.procedural_kind);
      return e4::from_scalar(gkr_virtual_base_value(kind, output_index));
    }
    if (input_slot.origin == BWD_COEFF_ORIGIN_READ_EXT) {
      const e4 *input = bwd_main_cont_window_column<e4>(desc, record.src);
      return load<e4, ld_modifier::cs>(input, output_index);
    }
    const bf *input = bwd_main_cont_window_column<bf>(desc, record.src);
    return e4::from_scalar(load<bf, ld_modifier::cs>(input, output_index));
  }
  const u32 leaf_index = output_index << 3;
  if (input_slot.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
    const gkr_base_source_kind kind = bwd_coeff_procedural_source_kind(input_slot.procedural_kind);
    bwd_main_cont_bf8 leaves;
#pragma unroll
    for (u32 q = 0; q < 8; q++)
      leaves.value[q] = gkr_virtual_base_value(kind, leaf_index + q);
    return bwd_main_cont_fold_bf_wide(leaves);
  }
  if (input_slot.origin == BWD_COEFF_ORIGIN_READ_EXT) {
    const e4 *input = bwd_main_cont_window_column<e4>(desc, record.src) + leaf_index;
    bwd_main_cont_e4_pair packets[4];
#pragma unroll
    for (u32 pair = 0; pair < 4; pair++)
      packets[pair] = load<bwd_main_cont_e4_pair, ld_modifier::cs>(reinterpret_cast<const bwd_main_cont_e4_pair *>(input) + pair);
    return bwd_main_cont_fold_e4_wide(packets);
  }
  const bf *input = bwd_main_cont_window_column<bf>(desc, record.src) + leaf_index;
  const bwd_main_cont_bf8 leaves = load<bwd_main_cont_bf8, ld_modifier::cs>(reinterpret_cast<const bwd_main_cont_bf8 *>(input));
  return bwd_main_cont_fold_bf_wide(leaves);
}

// Retain the accepted fused pair geometry; only fold arithmetic changes.
DEVICE_FORCEINLINE void bwd_main_cont_wide_prologue(const bwd_main_cont_window_desc &desc) {
  const u32 lane = threadIdx.x & 31;
  const u32 warp = threadIdx.x >> 5;
  const u32 logical_rows = bwd_main_cont_logical_rows(desc.eq_sizes);
  for (u32 subrow = 0; subrow < 4; ++subrow) {
    const u32 row = blockIdx.x * 32 + subrow * 8 + lane / 4;
    const bool active = row < logical_rows;
    for (u32 position = desc.fold_list_offsets[warp]; position < desc.fold_list_offsets[warp + 1]; ++position) {
      const auto record = desc.source[desc.fold_sources[position]];
      const auto &input = desc.slot[bwd_main_cont_window_lane_slot(record.src)];
      const u32 index = ((active ? row : 0) << 3) + 2 * (lane % 4);
      bwd_main_cont_e4_pair values;
#pragma unroll
      for (u32 offset = 0; offset < 2; ++offset)
        values.value[offset] = bwd_main_cont_fold_output_wide(desc, record, input, index + offset);
      if (active)
        store<bwd_main_cont_e4_pair, st_modifier::wb>(reinterpret_cast<bwd_main_cont_e4_pair *>(bwd_main_cont_window_column_mut(desc, record.publish) + index),
                                                      values);
    }
  }
  __syncthreads();
}

template <u16 Shape, bool StaticX0> DEVICE_FORCEINLINE void bwd_main_cont_wide_execute(const bwd_main_cont_window_desc &desc) {
  bwd_main_cont_wide_prologue(desc);
  switch ((threadIdx.x >> 5) / 3) {
  case 0:
    bwd_main_cont_fused_dispatch_x0<Shape, 0, StaticX0, true, StaticX0 ? 0 : 48, 1024>(desc);
    break;
  case 1:
    bwd_main_cont_fused_dispatch_x0<Shape, 1, StaticX0, true, StaticX0 ? 0 : 48, 1024>(desc);
    break;
  case 2:
    bwd_main_cont_fused_dispatch_x0<Shape, 2, StaticX0, true, StaticX0 ? 0 : 48, 1024>(desc);
    break;
  }
}

#define AB_GKR_MAIN_CONT_DEFINE_WIDE(Name, Shape, StaticX0)                                                                                                    \
  EXTERN __global__ __launch_bounds__(288, 2) void Name(const __grid_constant__ bwd_main_cont_window_desc desc) {                                              \
    if (blockDim.x != 288 || gridDim.x != desc.row_tiles || desc.publication_fold != 3 || desc.source_count > BWD_MAIN_CONT_WINDOW_MAX_SOURCES ||              \
        desc.fold_list_offsets[BWD_MAIN_CONT_WINDOW_WARPS] != desc.source_count || desc.program_words > BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP ||               \
        desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM != 0)                                                                                             \
      return;                                                                                                                                                  \
    bwd_main_cont_wide_execute<Shape, StaticX0>(desc);                                                                                                         \
  }

// Compare against lane8 publication with identical input/output geometry.
EXTERN __global__ __launch_bounds__(96) void ab_gkr_main_cont_fold_wide_publish(const __grid_constant__ bwd_main_cont_window_desc desc) {
  if (blockDim.x != 96 || gridDim.x != desc.row_tiles * 24)
    return;
  const u32 lane = threadIdx.x & 31;
  const u32 block_in_tile = blockIdx.x % 24;
  const u32 fold_warp = 3 * (block_in_tile / 8) + (threadIdx.x >> 5);
  const u32 row = (blockIdx.x / 24) * 32 + (block_in_tile % 8) * 4 + lane / 8;
  const bool active = row < bwd_main_cont_logical_rows(desc.eq_sizes);
  const u32 index = ((active ? row : 0) << 3) + lane % 8;
  for (u32 position = desc.fold_list_offsets[fold_warp]; position < desc.fold_list_offsets[fold_warp + 1]; ++position) {
    const auto record = desc.source[desc.fold_sources[position]];
    const auto &input = desc.slot[bwd_main_cont_window_lane_slot(record.src)];
    const e4 value = bwd_main_cont_fold_output_wide(desc, record, input, index);
    if (active)
      store<e4, st_modifier::wb>(bwd_main_cont_window_column_mut(desc, record.publish), value, index);
  }
}

} // namespace airbender::gkr::backward
