#pragma once

#include "../../backward/window/common.cuh"
#include "primitives/proth120.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

constexpr u32 BWD_PR_MAIN_CONT_BLOCK_THREADS = 96;
constexpr u32 BWD_PR_MAIN_CONT_WARPS = 3;
constexpr u32 BWD_PR_MAIN_CONT_FOLD_LISTS = 3;
constexpr u32 BWD_PR_MAIN_CONT_FOLD_LIST_ENDPOINTS = BWD_PR_MAIN_CONT_FOLD_LISTS + 1;
constexpr u32 BWD_PR_MAIN_CONT_ROWS_PER_TILE = 32;
constexpr u32 BWD_PR_MAIN_CONT_TENSOR_CELLS = 27;
constexpr u32 BWD_PR_MAIN_CONT_LANES_PER_ROW = 4;
constexpr u32 BWD_PR_MAIN_CONT_ROWS_PER_PASS = BWD_WINDOW_WARP_LANES / BWD_PR_MAIN_CONT_LANES_PER_ROW;
constexpr u32 BWD_PR_MAIN_CONT_SUBROWS = BWD_PR_MAIN_CONT_ROWS_PER_TILE / BWD_PR_MAIN_CONT_ROWS_PER_PASS;
constexpr u32 BWD_PR_MAIN_CONT_FOLD_WEIGHTS = 7;
constexpr u32 BWD_PR_MAIN_CONT_PROGRAM_WORD_CAP = 8192;
constexpr u32 BWD_PR_MAIN_CONT_MAX_SOURCES = 1072;
constexpr u32 BWD_PR_MAIN_CONT_ADDR_SLOTS = 64;

struct alignas(2) bwd_pr_main_cont_source_record {
  u16 src;
  u16 publish;
};

struct alignas(16) bwd_pr_main_cont_desc {
  u16 program[BWD_PR_MAIN_CONT_PROGRAM_WORD_CAP];
  u16 program_words;
  u16 source_count;
  u16 fold_list_offsets[BWD_PR_MAIN_CONT_FOLD_LIST_ENDPOINTS];
  u16 fold_sources[BWD_PR_MAIN_CONT_MAX_SOURCES];
  bwd_pr_main_cont_source_record source[BWD_PR_MAIN_CONT_MAX_SOURCES];
  u16 reserved0[2];
  bwd_source_window slot[BWD_PR_MAIN_CONT_ADDR_SLOTS];
  const pr *coefficients;
  const pr *immediates;
  const pr *fold_weights;
  const pr *eq_high;
  const pr *eq_low;
  pr *partials;
  u32 c_init_coeff;
  u32 row_tiles;
  gkr_eq_sizes eq_sizes;
  u32 reserved1[3];
};

struct alignas(32) bwd_pr_pair {
  pr value[2];
};

static_assert(BWD_PR_MAIN_CONT_PROGRAM_WORD_CAP == BWD_CONTINUATION_PROGRAM_WORD_CAP, "continuation program capacity drift");
static_assert(BWD_PR_MAIN_CONT_MAX_SOURCES == BWD_CONTINUATION_MAX_SOURCES, "continuation source capacity drift");
static_assert(BWD_PR_MAIN_CONT_MAX_SOURCES < BWD_PROGRAM_SOURCE_NONE, "semantic SourceId collides with source-none sentinel");
static_assert(BWD_PR_MAIN_CONT_ADDR_SLOTS == BWD_SOURCE_WINDOW_SLOTS, "continuation address capacity drift");
static_assert(BWD_PR_MAIN_CONT_ADDR_SLOTS * (1u << BWD_SOURCE_LANE_COLUMN_BITS) <= BWD_SOURCE_LANE_NONE, "continuation lane collides with lane-none");
static_assert(BWD_PR_MAIN_CONT_BLOCK_THREADS == BWD_PR_MAIN_CONT_WARPS * BWD_WINDOW_WARP_LANES, "one warp per x0 selector");
static_assert(BWD_PR_MAIN_CONT_FOLD_LISTS == BWD_PR_MAIN_CONT_WARPS, "one fold list per warp");
static_assert(BWD_PR_MAIN_CONT_TENSOR_CELLS == 27, "continuation tensor geometry drift");
static_assert(BWD_PR_MAIN_CONT_ROWS_PER_TILE == BWD_WINDOW_WARP_LANES, "continuation row tile drift");
static_assert(BWD_PR_MAIN_CONT_SUBROWS * BWD_PR_MAIN_CONT_ROWS_PER_PASS == BWD_PR_MAIN_CONT_ROWS_PER_TILE, "fold prologue tile coverage drift");
static_assert(BWD_PR_MAIN_CONT_FOLD_WEIGHTS == BWD_FOLD_WEIGHT_SLOTS - BWD_FOLD_WEIGHT_BASE_D3, "depth-three fold weight drift");
static_assert(BWD_CONTINUATION_CLASS_C0_LINEAR_E4 == 0, "continuation linear class drift");
static_assert(BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4 == 1, "continuation dual-product class drift");
static_assert(BWD_CONTINUATION_CLASS_GROUP_HEADER == 2, "continuation group class drift");
static_assert(sizeof(bwd_pr_pair) == 32 && alignof(bwd_pr_pair) == 32, "pr pair must be one aligned 256-bit transaction");

static_assert(sizeof(bwd_pr_main_cont_source_record) == 4, "continuation source-record ABI size drift");
static_assert(alignof(bwd_pr_main_cont_source_record) == 2, "continuation source-record ABI alignment drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_source_record, src) == 0, "continuation source src offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_source_record, publish) == 2, "continuation source publish offset drift");

static_assert(sizeof(bwd_pr_main_cont_desc) == 23936, "pr continuation descriptor ABI size drift");
static_assert(alignof(bwd_pr_main_cont_desc) == 16, "pr continuation descriptor ABI alignment drift");
static_assert(sizeof(bwd_pr_main_cont_desc) + 2048 <= BWD_WINDOW_DESC_CAP, "pr continuation descriptor lacks argument headroom");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, program) == 0, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, program_words) == 16384, "program_words ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, source_count) == 16386, "source_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, fold_list_offsets) == 16388, "fold_list_offsets ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, fold_sources) == 16396, "fold_sources ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, source) == 18540, "source ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, reserved0) == 22828, "reserved0 ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, slot) == 22832, "slot ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, coefficients) == 23856, "coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, immediates) == 23864, "immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, fold_weights) == 23872, "fold_weights ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, eq_high) == 23880, "eq_high ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, eq_low) == 23888, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, partials) == 23896, "partials ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, c_init_coeff) == 23904, "c_init_coeff ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, row_tiles) == 23908, "row_tiles ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, eq_sizes) == 23912, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_cont_desc, reserved1) == 23924, "reserved1 ABI offset drift");

DEVICE_FORCEINLINE const pr *bwd_pr_main_cont_column(const bwd_pr_main_cont_desc &desc, const u16 lane) {
  const bwd_source_window &slot = desc.slot[bwd_source_lane_slot(lane)];
  return reinterpret_cast<const pr *>(slot.base) + (static_cast<size_t>(bwd_source_lane_column(lane)) << slot.log2_stride);
}

DEVICE_FORCEINLINE pr *bwd_pr_main_cont_column_mut(const bwd_pr_main_cont_desc &desc, const u16 lane) {
  return const_cast<pr *>(bwd_pr_main_cont_column(desc, lane));
}

DEVICE_FORCEINLINE u32 bwd_pr_main_cont_logical_rows(const gkr_eq_sizes &sizes) { return 1u << (sizes.high[0] + sizes.high[1] + sizes.low); }

DEVICE_FORCEINLINE pr bwd_pr_virtual_base_value(const u8 procedural_kind, const u32 row) {
  u32 value = 0;
  switch (bwd_coeff_procedural_source_kind(procedural_kind)) {
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS:
    value = row < (1u << 16) ? row : 0u;
    break;
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP:
    value = row < (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS) ? row : 0u;
    break;
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW:
    value = (row << 2) & 0xffffu;
    break;
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH:
    value = row >> 14;
    break;
  default:
    break;
  }
  const u32 natural[4] = {value, 0, 0, 0};
  return pr::from_u128_with_reduction(natural);
}

DEVICE_FORCEINLINE pr bwd_pr_main_cont_fold_step(const pr accumulator, const pr leaf, const pr leaf0, const pr weight) {
  return pr::add(accumulator, pr::mul(weight, pr::sub(leaf, leaf0)));
}

DEVICE_FORCEINLINE pr bwd_pr_main_cont_fold_output(const bwd_pr_main_cont_desc &desc, const u16 src, const bwd_source_window &input_slot,
                                                   const u32 output_index, const pr (&weights)[BWD_PR_MAIN_CONT_FOLD_WEIGHTS]) {
  const u32 leaf_index = output_index << 3;
  if (input_slot.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
    const pr leaf0 = bwd_pr_virtual_base_value(input_slot.procedural_kind, leaf_index);
    pr accumulator = leaf0;
#pragma unroll
    for (u32 q = 1; q < 8; q++)
      accumulator = bwd_pr_main_cont_fold_step(accumulator, bwd_pr_virtual_base_value(input_slot.procedural_kind, leaf_index + q), leaf0, weights[q - 1]);
    return accumulator;
  }
  const auto *packets = reinterpret_cast<const bwd_pr_pair *>(bwd_pr_main_cont_column(desc, src) + leaf_index);
  const bwd_pr_pair first = load<bwd_pr_pair, ld_modifier::cs>(packets);
  const pr leaf0 = first.value[0];
  pr accumulator = bwd_pr_main_cont_fold_step(leaf0, first.value[1], leaf0, weights[0]);
#pragma unroll
  for (u32 pair = 1; pair < 4; pair++) {
    const bwd_pr_pair packet = load<bwd_pr_pair, ld_modifier::cs>(packets + pair);
    accumulator = bwd_pr_main_cont_fold_step(accumulator, packet.value[0], leaf0, weights[2 * pair - 1]);
    accumulator = bwd_pr_main_cont_fold_step(accumulator, packet.value[1], leaf0, weights[2 * pair]);
  }
  return accumulator;
}

DEVICE_FORCEINLINE void bwd_pr_main_cont_fold_source_pair(const bwd_pr_main_cont_desc &desc, const u16 source_id, const u32 row, const u32 corner_pair,
                                                          const pr (&weights)[BWD_PR_MAIN_CONT_FOLD_WEIGHTS]) {
  const bwd_pr_main_cont_source_record record = desc.source[source_id];
  const bwd_source_window &input_slot = desc.slot[bwd_source_lane_slot(record.src)];
  const u32 output_index = (row << 3) + 2 * corner_pair;
  const bwd_pr_pair values{{bwd_pr_main_cont_fold_output(desc, record.src, input_slot, output_index, weights),
                            bwd_pr_main_cont_fold_output(desc, record.src, input_slot, output_index + 1, weights)}};
  pr *publish = bwd_pr_main_cont_column_mut(desc, record.publish) + output_index;
  store<bwd_pr_pair, st_modifier::wb>(reinterpret_cast<bwd_pr_pair *>(publish), values);
}

DEVICE_FORCEINLINE void bwd_pr_main_cont_fold_prologue(const bwd_pr_main_cont_desc &desc, const u32 warp, const u32 row, const u32 corner_pair,
                                                       const pr (&weights)[BWD_PR_MAIN_CONT_FOLD_WEIGHTS]) {
  const u32 begin = desc.fold_list_offsets[warp];
  const u32 end = desc.fold_list_offsets[warp + 1];
  for (u32 position = begin; position < end; position++)
    bwd_pr_main_cont_fold_source_pair(desc, desc.fold_sources[position], row, corner_pair, weights);
}

} // namespace airbender::gkr::proth120::backward
