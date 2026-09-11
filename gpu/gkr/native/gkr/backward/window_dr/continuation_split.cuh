#pragma once

#include "continuation_packed.cuh"

namespace airbender::gkr::backward {

DEVICE_FORCEINLINE u32 dr_cont_dense_slot(const u32 enabled_mask, const u32 dense) {
  u32 seen = 0;
#pragma unroll
  for (u32 slot = 0; slot < GKR_DIM_REDUCING_SLOTS; ++slot) {
    if ((enabled_mask & (1u << slot)) != 0) {
      if (seen++ == dense)
        return slot;
    }
  }
  return GKR_DIM_REDUCING_SLOTS;
}

// Host preflight rejects cross-slot aliases. Within-slot aliases retain the
// first-access guard, so every canonical output pair has exactly one writer.
DEVICE_FORCEINLINE void dr_cont_selected_slot_prologue(const gkr_dr_cont_window3_desc &desc, const u32 slot) {
  constexpr u32 work_count = GKR_DIM_REDUCING_INPUTS_PER_SLOT * DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t tile_pair_base = static_cast<size_t>(blockIdx.x) * DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t output_pair_count = static_cast<size_t>(1u) << (desc.log_rows + 3u);
  for (u32 work = threadIdx.x; work < work_count; work += blockDim.x) {
    const u32 operand = work / DR_WINDOW_CONT_PAIRS_PER_TILE;
    const size_t output_pair = tile_pair_base + work % DR_WINDOW_CONT_PAIRS_PER_TILE;
    const auto source = gkr_resolve_dim_reducing_continuation_source<e4>(desc.batch.tables, desc.batch.slots[slot].io[operand]);
    const bool active = source.first_access && output_pair < output_pair_count;
    const auto folded = dr_window_fold_depth3_pair(desc, source.previous_layer_start, output_pair, active);
    if (active)
      store<dr_window_e4_pair, st_modifier::cs>(reinterpret_cast<dr_window_e4_pair *>(source.this_layer_start) + output_pair, folded);
  }
}

DEVICE_FORCEINLINE void dr_cont_packed_evaluate(const gkr_dr_cont_window3_desc &desc, const u32 effective_mask) {
  const u32 lane = bwd_window_lane();
  const u32 row_tile = bwd_window_row_tile();
  const u32 row = row_tile * BWD_WINDOW_ROWS_PER_TILE + lane;
  const bool active = row < (1u << desc.log_rows);
  const u32 safe_row = active ? row : 0;
  const auto selector = bwd_window_selector(bwd_window_selector_id());
  dr_window_packed_carry_e4 total[3] = {};
  if (effective_mask & (1u << 0))
    dr_cont_recompute_slot_body<0>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 1))
    dr_cont_recompute_slot_body<1>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 2))
    dr_cont_recompute_slot_body<2>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 3))
    dr_cont_recompute_slot_body<3>(desc, safe_row, selector, total);
  if (effective_mask & (1u << 4))
    dr_cont_recompute_slot_body<4>(desc, safe_row, selector, total);
  const e4 values[3] = {total[0].reduce(), total[1].reduce(), total[2].reduce()};
  const size_t tile_slot = static_cast<size_t>(blockIdx.y) * gridDim.x + row_tile;
  dr_cont_quartet_publish(desc, tile_slot, lane, active, safe_row, selector, values);
}

DEVICE_FORCEINLINE void dr_cont_packed_unified(const gkr_dr_cont_window3_desc &desc) {
  u32 effective_mask = desc.batch.enabled_mask;
  if (gridDim.y == 1) {
    dr_window_continuation_prologue(desc);
  } else {
    const u32 slot = dr_cont_dense_slot(effective_mask, blockIdx.y);
    if (slot >= GKR_DIM_REDUCING_SLOTS)
      return;
    effective_mask = 1u << slot;
    dr_cont_selected_slot_prologue(desc, slot);
  }
  __syncthreads();
  dr_cont_packed_evaluate(desc, effective_mask);
}

} // namespace airbender::gkr::backward
