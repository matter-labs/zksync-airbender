#pragma once

// Dedicated width-three continuation-window ABI. The shared segmented-VM
// header supplies address lanes, coefficient-bank access, fold weights, Eq
// geometry and procedural-source primitives; this descriptor carries no R0
// source-class or per-round publication semantics.
#include "../segmented_vm.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP = 6472;
constexpr u32 BWD_MAIN_CONT_WINDOW_MAX_SOURCES = 1072;
constexpr u32 BWD_MAIN_CONT_WINDOW_ADDR_SLOTS = 64;
constexpr u32 BWD_MAIN_CONT_WINDOW_MAX_IMMEDIATES = 512;
// Nine logical selector/fold lists are partitioned across three blocks of
// three physical warps. Each physical warp still owns exactly one selector.
constexpr u32 BWD_MAIN_CONT_WINDOW_WARPS = 9;
constexpr u32 BWD_MAIN_CONT_WINDOW_BLOCK_WARPS = 3;
constexpr u32 BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS = 3;
constexpr u32 BWD_MAIN_CONT_WINDOW_FOLD_LIST_ENDPOINTS = BWD_MAIN_CONT_WINDOW_WARPS + 1;
constexpr u32 BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE = 32;
constexpr u32 BWD_MAIN_CONT_WINDOW_TENSOR_CELLS = 27;
constexpr u32 BWD_MAIN_CONT_WINDOW_BLOCK_THREADS = 96;
constexpr u32 BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS = BWD_MAIN_CONT_WINDOW_BLOCK_WARPS * BWD_SEG_WARP_LANES;
constexpr u32 BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW = 4;
constexpr u32 BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK = BWD_SEG_WARP_LANES / BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;
constexpr u32 BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE = BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE / BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK;
constexpr u32 BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE = BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS * BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;
constexpr u32 BWD_MAIN_CONT_WINDOW_DYNAMIC_X0 = 3;

constexpr u16 BWD_MAIN_CONT_WINDOW_SHAPE_PLAIN_LINEAR = 1u << 0;
constexpr u16 BWD_MAIN_CONT_WINDOW_SHAPE_GROUPED = 1u << 1;
constexpr u16 BWD_MAIN_CONT_WINDOW_SHAPE_C_INIT = 1u << 2;
constexpr u16 BWD_MAIN_CONT_WINDOW_SHAPE_BANKED_GROUP_IMMEDIATE = 1u << 3;
constexpr u16 BWD_MAIN_CONT_WINDOW_SHAPE_NEGATIVE_GROUP_IMMEDIATE = 1u << 4;
constexpr u16 BWD_MAIN_CONT_WINDOW_SHAPE_DEFINED_BITS = 0x1f;

struct alignas(2) bwd_main_cont_window_source_record {
  u16 src;
  u16 publish;
};

struct alignas(16) bwd_main_cont_window_desc {
  u16 program[BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP];
  u16 program_words;
  u16 source_count;
  u16 fold_list_offsets[BWD_MAIN_CONT_WINDOW_FOLD_LIST_ENDPOINTS];
  u16 fold_sources[BWD_MAIN_CONT_WINDOW_MAX_SOURCES];
  bwd_main_cont_window_source_record source[BWD_MAIN_CONT_WINDOW_MAX_SOURCES];
  bwd_seg_addr_slot slot[BWD_MAIN_CONT_WINDOW_ADDR_SLOTS];
  u32 c_init_coeff;
  u32 immediates[BWD_MAIN_CONT_WINDOW_MAX_IMMEDIATES];
  u32 publication_fold;
  const e4 *eq_low;
  e4 *partials;
  u32 row_tiles;
  gkr_eq_sizes eq_sizes;
};

static_assert(BWD_MAIN_CONT_WINDOW_PROGRAM_WORD_CAP == BWD_SEG_PROGRAM_WORD_CAP, "continuation program capacity drift");
static_assert(BWD_MAIN_CONT_WINDOW_MAX_SOURCES == BWD_SEG_MAX_SOURCES, "continuation source capacity drift");
static_assert(BWD_MAIN_CONT_WINDOW_ADDR_SLOTS == BWD_SEG_ADDR_SLOTS, "continuation address capacity drift");
static_assert(BWD_MAIN_CONT_WINDOW_MAX_IMMEDIATES == BWD_SEG_MAX_IMMEDIATES, "continuation immediate capacity drift");
static_assert(BWD_MAIN_CONT_WINDOW_MAX_SOURCES < BWD_SEG_SOURCE_NONE, "semantic SourceId collides with source-none sentinel");
static_assert(BWD_MAIN_CONT_WINDOW_ADDR_SLOTS * (1u << BWD_SEG_ADDR_COLUMN_BITS) <= BWD_SEG_ADDR_NONE,
              "continuation address lane collides with lane-none sentinel");
static_assert(BWD_MAIN_CONT_WINDOW_BLOCK_THREADS == BWD_MAIN_CONT_WINDOW_BLOCK_WARPS * BWD_SEG_WARP_LANES, "one physical warp per selector");
static_assert(BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS == 96, "publication block covers one fold-list partition");
static_assert(BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW == 4, "publication uses one lane per aligned corner pair");
static_assert(BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK == 8, "publication block row coverage drift");
static_assert(BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE == 4, "publication tile partition drift");
static_assert(BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE == 12, "publication blocks-per-tile drift");
static_assert(BWD_MAIN_CONT_WINDOW_DYNAMIC_X0 == 3, "dynamic x0 sentinel must follow the ternary selectors");
static_assert(BWD_MAIN_CONT_WINDOW_WARPS == BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS * BWD_MAIN_CONT_WINDOW_BLOCK_WARPS,
              "selector-block partition must cover every logical selector");
static_assert(BWD_MAIN_CONT_WINDOW_TENSOR_CELLS == 3 * BWD_MAIN_CONT_WINDOW_WARPS, "continuation tensor geometry drift");
static_assert(BWD_MAIN_CONT_WINDOW_ROWS_PER_TILE == BWD_SEG_WARP_LANES, "continuation row tile drift");
static_assert(BWD_MAIN_CONT_WINDOW_SHAPE_DEFINED_BITS == 0x1f, "continuation shape width drift");
static_assert(BWD_SEG_EXT_CLASS_C0_LINEAR_E4 == 0, "continuation linear class drift");
static_assert(BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4 == 1, "continuation dual-product class drift");
static_assert(BWD_SEG_EXT_CLASS_GROUP_HEADER == 2, "continuation group class drift");

static_assert(sizeof(bwd_main_cont_window_source_record) == 4, "continuation source-record ABI size drift");
static_assert(alignof(bwd_main_cont_window_source_record) == 2, "continuation source-record ABI alignment drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_source_record, src) == 0, "continuation source src offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_source_record, publish) == 2, "continuation source publish offset drift");

static_assert(sizeof(bwd_main_cont_window_desc) == 22512, "continuation descriptor ABI size drift");
static_assert(alignof(bwd_main_cont_window_desc) == 16, "continuation descriptor ABI alignment drift");
static_assert(sizeof(bwd_main_cont_window_desc) <= BWD_SEG_DESC_CAP, "continuation descriptor exceeds kernel-argument ceiling");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, program) == 0, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, program_words) == 12944, "program_words ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, source_count) == 12946, "source_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, fold_list_offsets) == 12948, "fold_list_offsets ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, fold_sources) == 12968, "fold_sources ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, source) == 15112, "source ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, slot) == 19400, "slot ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, c_init_coeff) == 20424, "c_init_coeff ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, immediates) == 20428, "immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, publication_fold) == 22476, "publication_fold ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, eq_low) == 22480, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, partials) == 22488, "partials ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, row_tiles) == 22496, "row_tiles ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_cont_window_desc, eq_sizes) == 22500, "eq_sizes ABI offset drift");

DEVICE_FORCEINLINE u32 bwd_main_cont_window_lane_slot(const u16 lane) { return u32{lane} >> BWD_SEG_ADDR_COLUMN_BITS; }
DEVICE_FORCEINLINE u32 bwd_main_cont_window_lane_column(const u16 lane) { return u32{lane} & BWD_SEG_ADDR_COLUMN_MASK; }

template <typename T> DEVICE_FORCEINLINE const T *bwd_main_cont_window_column(const bwd_main_cont_window_desc &desc, const u16 lane) {
  const bwd_seg_addr_slot &slot = desc.slot[bwd_main_cont_window_lane_slot(lane)];
  const T *base = reinterpret_cast<const T *>(slot.base);
  return base + (static_cast<size_t>(bwd_main_cont_window_lane_column(lane)) << slot.log2_stride);
}

DEVICE_FORCEINLINE e4 *bwd_main_cont_window_column_mut(const bwd_main_cont_window_desc &desc, const u16 lane) {
  return const_cast<e4 *>(bwd_main_cont_window_column<e4>(desc, lane));
}

} // namespace airbender::gkr::backward
