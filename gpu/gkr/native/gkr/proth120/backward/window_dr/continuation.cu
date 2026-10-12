#include "evaluate_pr.cuh"

namespace airbender::gkr::proth120::backward {

constexpr u32 PR_DR_WINDOW_CONT_PAIRS_PER_TILE = pr_dr_bwd::BWD_WINDOW_ROWS_PER_TILE * 8u;

struct alignas(32) pr_dr_window_cell_pair {
  pr value[2];
};

static_assert(sizeof(pr_dr_window_cell_pair) == 32 && alignof(pr_dr_window_cell_pair) == 32, "Proth120 DR continuation pair must be one 256-bit transaction");

DEVICE_FORCEINLINE pr_dr_window_cell_pair pr_dr_window_load_pair_guarded(const pr *source, const size_t pair_index, const bool active) {
  if (!active)
    return {{pr_zero(), pr_zero()}};
  return load<pr_dr_window_cell_pair, ld_modifier::cs>(reinterpret_cast<const pr_dr_window_cell_pair *>(source) + pair_index);
}

DEVICE_FORCEINLINE pr_dr_window_cell_pair pr_dr_window_pair_fold(const pr_dr_window_cell_pair zero, const pr_dr_window_cell_pair one, const pr challenge) {
  pr_dr_window_cell_pair result;
#pragma unroll
  for (u32 gate_bit = 0; gate_bit < 2; ++gate_bit)
    result.value[gate_bit] = pr::fma(challenge, pr::sub(one.value[gate_bit], zero.value[gate_bit]), zero.value[gate_bit]);
  return result;
}

DEVICE_FORCEINLINE pr_dr_window_cell_pair pr_dr_window_fold_depth3_pair(const pr_dr_window_desc &desc, const pr *source, const size_t output_pair,
                                                                        const bool active) {
  const pr c0 = active ? load<pr, ld_modifier::cs>(desc.claim_point, desc.start_round - 3u) : pr_zero();
  const pr c1 = active ? load<pr, ld_modifier::cs>(desc.claim_point, desc.start_round - 2u) : pr_zero();
  const pr c2 = active ? load<pr, ld_modifier::cs>(desc.claim_point, desc.start_round - 1u) : pr_zero();
  pr_dr_window_cell_pair level2[2];
#pragma unroll
  for (u32 half = 0; half < 2; ++half) {
    const size_t leaf_pair = (output_pair << 3) + 4u * half;
    const auto first =
        pr_dr_window_pair_fold(pr_dr_window_load_pair_guarded(source, leaf_pair, active), pr_dr_window_load_pair_guarded(source, leaf_pair + 1u, active), c0);
    const auto second = pr_dr_window_pair_fold(pr_dr_window_load_pair_guarded(source, leaf_pair + 2u, active),
                                               pr_dr_window_load_pair_guarded(source, leaf_pair + 3u, active), c0);
    level2[half] = pr_dr_window_pair_fold(first, second, c1);
  }
  return pr_dr_window_pair_fold(level2[0], level2[1], c2);
}

DEVICE_FORCEINLINE u32 pr_dr_window_dense_slot(u32 enabled_mask, const u32 dense) {
  for (u32 index = 0; index < dense; ++index)
    enabled_mask &= enabled_mask - 1;
  return __ffs(enabled_mask) - 1;
}

DEVICE_FORCEINLINE void pr_dr_window_selected_slot_prologue(const pr_dr_window_desc &desc, const u32 slot) {
  constexpr u32 work_count = GKR_DIM_REDUCING_INPUTS_PER_SLOT * PR_DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t tile_pair_base = static_cast<size_t>(blockIdx.x) * PR_DR_WINDOW_CONT_PAIRS_PER_TILE;
  const size_t output_pair_count = static_cast<size_t>(1u) << (desc.log_rows + 3u);
  for (u32 work = threadIdx.x; work < work_count; work += blockDim.x) {
    const u32 operand = work / PR_DR_WINDOW_CONT_PAIRS_PER_TILE;
    const size_t output_pair = tile_pair_base + work % PR_DR_WINDOW_CONT_PAIRS_PER_TILE;
    const auto source = gkr_resolve_dim_reducing_continuation_source<pr>(desc.batch.tables, desc.batch.slots[slot].inputs[operand]);
    const bool active = source.first_access && output_pair < output_pair_count;
    const auto folded = pr_dr_window_fold_depth3_pair(desc, source.previous_layer_start, output_pair, active);
    if (active)
      store<pr_dr_window_cell_pair, st_modifier::cs>(reinterpret_cast<pr_dr_window_cell_pair *>(source.this_layer_start) + output_pair, folded);
  }
}

EXTERN __global__ __launch_bounds__(pr_dr_bwd::BWD_WINDOW_BLOCK_THREADS,
                                    2) void ab_pr_gkr_bwd_dr_window_continuation_kernel(const __grid_constant__ pr_dr_window_desc desc) {
  const u32 slot = pr_dr_window_dense_slot(desc.batch.enabled_mask, blockIdx.y);
  pr_dr_window_selected_slot_prologue(desc, slot);
  __syncthreads();
  const size_t tile_slot = static_cast<size_t>(blockIdx.y) * gridDim.x + blockIdx.x;
  pr_dr_window_evaluate<true>(desc, 1u << slot, tile_slot);
}

} // namespace airbender::gkr::proth120::backward
