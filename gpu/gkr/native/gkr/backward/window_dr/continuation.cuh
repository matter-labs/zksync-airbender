#pragma once

#include "gkr/backward/window/window_geometry.cuh"
#include "gkr/support/lookup_helpers.cuh"

namespace airbender::gkr::backward {

constexpr u32 DR_WINDOW_CONT_PAIRS_PER_TILE = BWD_WINDOW_ROWS_PER_TILE * 8u;

template <typename F> struct alignas(32) dr_window_cell_pair {
  F value[2];
};

template <typename F> DEVICE_FORCEINLINE dr_window_cell_pair<F> dr_window_load_pair_guarded(const F *source, const size_t pair_index, const bool active) {
  if (!active)
    return {{F::ZERO(), F::ZERO()}};
  return load<dr_window_cell_pair<F>, ld_modifier::cs>(reinterpret_cast<const dr_window_cell_pair<F> *>(source) + pair_index);
}

template <typename F>
DEVICE_FORCEINLINE dr_window_cell_pair<F> dr_window_pair_fold(const dr_window_cell_pair<F> zero, const dr_window_cell_pair<F> one, const F challenge) {
  dr_window_cell_pair<F> result;
#pragma unroll
  for (u32 gate_bit = 0; gate_bit < 2; ++gate_bit)
    result.value[gate_bit] = F::fma(challenge, F::sub(one.value[gate_bit], zero.value[gate_bit]), zero.value[gate_bit]);
  return result;
}

DEVICE_FORCEINLINE u32 dr_cont_dense_slot(u32 enabled_mask, const u32 dense) {
  for (u32 index = 0; index < dense; ++index)
    enabled_mask &= enabled_mask - 1;
  return __ffs(enabled_mask) - 1;
}

// The compiler rejects cross-slot aliases when it lowers the window. Within-slot aliases retain the
// first-access guard, so every canonical output pair has exactly one writer.
template <typename F, typename Descriptor> DEVICE_FORCEINLINE void dr_cont_selected_slot_prologue(const Descriptor &desc, const u32 slot) {
  constexpr u32 work_count = GKR_DIM_REDUCING_INPUTS_PER_SLOT * DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t tile_pair_base = static_cast<size_t>(blockIdx.x) * DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t output_pair_count = static_cast<size_t>(1u) << (desc.log_rows + 3u);
  for (u32 work = threadIdx.x; work < work_count; work += blockDim.x) {
    const u32 operand = work / DR_WINDOW_CONT_PAIRS_PER_TILE;
    const size_t output_pair = tile_pair_base + work % DR_WINDOW_CONT_PAIRS_PER_TILE;
    const auto source = gkr_resolve_dim_reducing_continuation_source<F>(desc.batch.tables, desc.batch.slots[slot].inputs[operand]);
    const bool active = source.first_access && output_pair < output_pair_count;
    const auto folded = dr_window_fold_depth3_pair(desc, source.previous_layer_start, output_pair, active);
    if (active)
      store<dr_window_cell_pair<F>, st_modifier::cs>(reinterpret_cast<dr_window_cell_pair<F> *>(source.this_layer_start) + output_pair, folded);
  }
}

} // namespace airbender::gkr::backward
