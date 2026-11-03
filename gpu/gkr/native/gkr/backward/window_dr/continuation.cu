#include "evaluate.cuh"

namespace airbender::gkr::backward {

constexpr u32 DR_WINDOW_CONT_PAIRS_PER_TILE = BWD_WINDOW_ROWS_PER_TILE * 8u;

struct alignas(32) dr_window_e4_pair {
  e4 value[2];
};

static_assert(sizeof(dr_window_e4_pair) == 32 && alignof(dr_window_e4_pair) == 32, "DR continuation pair must be one aligned 256-bit transaction");

DEVICE_FORCEINLINE dr_window_e4_pair dr_window_load_e4_pair_guarded(const e4 *source, const size_t pair_index, const bool active) {
  if (!active)
    return {{e4::ZERO(), e4::ZERO()}};
  return load<dr_window_e4_pair, ld_modifier::cs>(reinterpret_cast<const dr_window_e4_pair *>(source) + pair_index);
}

DEVICE_FORCEINLINE dr_window_e4_pair dr_window_pair_fold(const dr_window_e4_pair zero, const dr_window_e4_pair one, const e4 challenge) {
  dr_window_e4_pair result;
#pragma unroll
  for (u32 gate_bit = 0; gate_bit < 2; ++gate_bit)
    result.value[gate_bit] = e4::fma(challenge, e4::sub(one.value[gate_bit], zero.value[gate_bit]), zero.value[gate_bit]);
  return result;
}

// Fold all three preceding coordinates before publishing the input pairs.
DEVICE_FORCEINLINE dr_window_e4_pair dr_window_fold_depth3_pair(const gkr_dr_cont_window3_desc &desc, const e4 *source, const size_t output_pair,
                                                                const bool active) {
  const e4 c0 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 3u) : e4::ZERO();
  const e4 c1 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 2u) : e4::ZERO();
  const e4 c2 = active ? load<e4, ld_modifier::cs>(desc.claim_point, desc.start_round - 1u) : e4::ZERO();
  dr_window_e4_pair level1[4];
#pragma unroll
  for (u32 pair = 0; pair < 4; ++pair) {
    const size_t leaf_pair = (output_pair << 3) + 2u * pair;
    const auto zero = dr_window_load_e4_pair_guarded(source, leaf_pair, active);
    const auto one = dr_window_load_e4_pair_guarded(source, leaf_pair + 1u, active);
    level1[pair] = dr_window_pair_fold(zero, one, c0);
  }
  const auto level2_0 = dr_window_pair_fold(level1[0], level1[1], c1);
  const auto level2_1 = dr_window_pair_fold(level1[2], level1[3], c1);
  return dr_window_pair_fold(level2_0, level2_1, c2);
}

DEVICE_FORCEINLINE u32 dr_cont_dense_slot(u32 enabled_mask, const u32 dense) {
  for (u32 index = 0; index < dense; ++index)
    enabled_mask &= enabled_mask - 1;
  return __ffs(enabled_mask) - 1;
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
    const auto source = gkr_resolve_dim_reducing_continuation_source<e4>(desc.batch.tables, desc.batch.slots[slot].inputs[operand]);
    const bool active = source.first_access && output_pair < output_pair_count;
    const auto folded = dr_window_fold_depth3_pair(desc, source.previous_layer_start, output_pair, active);
    if (active)
      store<dr_window_e4_pair, st_modifier::cs>(reinterpret_cast<dr_window_e4_pair *>(source.this_layer_start) + output_pair, folded);
  }
}

EXTERN __global__ __launch_bounds__(BWD_WINDOW_BLOCK_THREADS, 2) void ab_gkr_dr_cont_window3_kernel(const __grid_constant__ gkr_dr_cont_window3_desc desc) {
  const u32 slot = dr_cont_dense_slot(desc.batch.enabled_mask, blockIdx.y);
  dr_cont_selected_slot_prologue(desc, slot);
  __syncthreads();
  const size_t tile_slot = static_cast<size_t>(blockIdx.y) * gridDim.x + blockIdx.x;
  dr_window_evaluate(desc, 1u << slot, tile_slot);
}

} // namespace airbender::gkr::backward
