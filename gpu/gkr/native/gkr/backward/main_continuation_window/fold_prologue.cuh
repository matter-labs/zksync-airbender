#pragma once

#include "main_continuation_window_abi.cuh"

namespace airbender::gkr::backward {

using ::airbender::primitives::memory::ld_modifier;
using ::airbender::primitives::memory::load;
using ::airbender::primitives::memory::st_modifier;
using ::airbender::primitives::memory::store;

struct alignas(32) bwd_main_cont_bf8 {
  bf value[8];
};

struct alignas(32) bwd_main_cont_e4_pair {
  e4 value[2];
};

static_assert(sizeof(bwd_main_cont_bf8) == 32 && alignof(bwd_main_cont_bf8) == 32, "BF leaf packet must be one aligned 256-bit load");
static_assert(sizeof(bwd_main_cont_e4_pair) == 32 && alignof(bwd_main_cont_e4_pair) == 32, "E4 pair must be one aligned 256-bit transaction");

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_bf_packet(const bwd_main_cont_bf8 &leaves) {
  constexpr u32 weight_base = BWD_SEG_FOLD_WEIGHT_BASE_D3;
  const bf leaf0 = leaves.value[0];
  e4 accumulator = e4::from_scalar(leaf0);
#pragma unroll
  for (u32 q = 1; q < 8; q++) {
    const e4 weight = ::ab_gkr_bwd_seg_fold_weights[weight_base + q - 1];
    accumulator = e4::fma(weight, bf::sub(leaves.value[q], leaf0), accumulator);
  }
  return accumulator;
}

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_e4_packets(const bwd_main_cont_e4_pair (&packets)[4]) {
  constexpr u32 weight_base = BWD_SEG_FOLD_WEIGHT_BASE_D3;
  const e4 leaf0 = packets[0].value[0];
  e4 accumulator = leaf0;
#pragma unroll
  for (u32 q = 1; q < 8; q++) {
    const e4 leaf = packets[q >> 1].value[q & 1];
    const e4 weight = ::ab_gkr_bwd_seg_fold_weights[weight_base + q - 1];
    accumulator = e4::fma(weight, e4::sub(leaf, leaf0), accumulator);
  }
  return accumulator;
}

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_output(const bwd_main_cont_window_desc &desc, const bwd_main_cont_window_source_record &record,
                                                const bwd_seg_addr_slot &input_slot, const u32 output_index) {
  const u32 leaf_index = output_index << 3;
  if (input_slot.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
    const gkr_base_source_kind kind = bwd_coeff_procedural_source_kind(input_slot.procedural_kind);
    bwd_main_cont_bf8 leaves;
#pragma unroll
    for (u32 q = 0; q < 8; q++)
      leaves.value[q] = gkr_virtual_base_value(kind, leaf_index + q);
    return bwd_main_cont_fold_bf_packet(leaves);
  }
  if (input_slot.origin == BWD_COEFF_ORIGIN_READ_EXT) {
    const e4 *input = bwd_main_cont_window_column<e4>(desc, record.src) + leaf_index;
    bwd_main_cont_e4_pair packets[4];
#pragma unroll
    for (u32 pair = 0; pair < 4; pair++)
      packets[pair] = load<bwd_main_cont_e4_pair, ld_modifier::cs>(reinterpret_cast<const bwd_main_cont_e4_pair *>(input) + pair);
    return bwd_main_cont_fold_e4_packets(packets);
  }
  const bf *input = bwd_main_cont_window_column<bf>(desc, record.src) + leaf_index;
  const bwd_main_cont_bf8 leaves = load<bwd_main_cont_bf8, ld_modifier::cs>(reinterpret_cast<const bwd_main_cont_bf8 *>(input));
  return bwd_main_cont_fold_bf_packet(leaves);
}

// Every lane publishes the eight Boolean corners for one suffix row. The input
// indices are `(row << 6) + (corner << 3) + q`: corner carries the three window
// coordinates and q carries the preceding delta-3 fold coordinates.
DEVICE_FORCEINLINE void bwd_main_cont_fold_source(const bwd_main_cont_window_desc &desc, const u16 source_id, const u32 row, const bool active) {
  const bwd_main_cont_window_source_record record = desc.source[source_id];
  const bwd_seg_addr_slot &input_slot = desc.slot[bwd_main_cont_window_lane_slot(record.src)];
  e4 outputs[8];
#pragma unroll
  for (u32 corner = 0; corner < 8; corner++)
    outputs[corner] = bwd_main_cont_fold_output(desc, record, input_slot, (row << 3) + corner);

  if (!active)
    return;
  e4 *publish = bwd_main_cont_window_column_mut(desc, record.publish) + (row << 3);
#pragma unroll
  for (u32 pair = 0; pair < 4; pair++) {
    const bwd_main_cont_e4_pair values{{outputs[2 * pair], outputs[2 * pair + 1]}};
    store<bwd_main_cont_e4_pair, st_modifier::wb>(reinterpret_cast<bwd_main_cont_e4_pair *>(publish) + pair, values);
  }
}

DEVICE_FORCEINLINE void bwd_main_cont_fold_prologue(const bwd_main_cont_window_desc &desc, const u32 warp_id, const u32 row, const bool active) {
  const u32 begin = desc.fold_list_offsets[warp_id];
  const u32 end = desc.fold_list_offsets[warp_id + 1];
  for (u32 position = begin; position < end; position++)
    bwd_main_cont_fold_source(desc, desc.fold_sources[position], row, active);
}

} // namespace airbender::gkr::backward
