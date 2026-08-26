#pragma once

#include "../../support/eq_inline.cuh"
#include "../../support/kernel_helpers.cuh"

namespace airbender::gkr {

constexpr u32 BWD_COEFF_HEADER_COEFFICIENT_BITS = 13;
constexpr u32 BWD_COEFF_HEADER_OPCODE_BITS = 3;
constexpr u32 BWD_COEFF_MAX_COEFFICIENT_ENCODINGS = 1u << BWD_COEFF_HEADER_COEFFICIENT_BITS;

constexpr u8 BWD_COEFF_ORIGIN_READ_BASE = 0;
constexpr u8 BWD_COEFF_ORIGIN_READ_EXT = 1;
constexpr u8 BWD_COEFF_ORIGIN_PROCEDURAL = 2;

constexpr u8 BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS = 0;
constexpr u8 BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP = 1;
constexpr u8 BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW = 2;
constexpr u8 BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH = 3;
constexpr u8 BWD_COEFF_PROCEDURAL_NONE = 0xff;

static_assert(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 1, "virtual kind order drift");
static_assert(GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 2, "virtual kind order drift");
static_assert(GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 3, "virtual kind order drift");

constexpr gkr_base_source_kind bwd_coeff_procedural_source_kind(const u8 procedural_kind) {
  return static_cast<gkr_base_source_kind>(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + procedural_kind);
}

struct bwd_source_window {
  const char *base;
  u8 log2_stride;
  u8 origin;
  u8 procedural_kind;
  u8 reserved[5];
};

static_assert(sizeof(bwd_source_window) == 16, "bwd_source_window ABI size drift");
static_assert(alignof(bwd_source_window) == 8, "bwd_source_window ABI alignment drift");

constexpr u16 BWD_SOURCE_LANE_NONE = 0xffff;
constexpr u32 BWD_SOURCE_LANE_COLUMN_BITS = 7;
constexpr u32 BWD_SOURCE_LANE_COLUMN_MASK = (1u << BWD_SOURCE_LANE_COLUMN_BITS) - 1u;
constexpr u32 BWD_SOURCE_WINDOW_SLOTS = 64;

DEVICE_FORCEINLINE u32 bwd_source_lane_slot(const u16 lane) { return u32{lane} >> BWD_SOURCE_LANE_COLUMN_BITS; }
DEVICE_FORCEINLINE u32 bwd_source_lane_column(const u16 lane) { return u32{lane} & BWD_SOURCE_LANE_COLUMN_MASK; }

constexpr u32 BWD_WINDOW_DESC_CAP = 32764;
constexpr u32 BWD_WINDOW_DESC_ALIGN = 16;
constexpr u32 BWD_WINDOW_WARP_LANES = 32;
constexpr u32 BWD_WINDOW_WARP_SHIFT = 5;
constexpr u32 BWD_WINDOW_LANE_INDEX_MASK = BWD_WINDOW_WARP_LANES - 1;
constexpr u32 BWD_COEFF_BANK_CAPACITY = 1792;
constexpr u32 BWD_COEFF_NONE = 0xffffffffu;
constexpr u32 BWD_CONTINUATION_MAX_SOURCES = 1072;
constexpr u32 BWD_CONTINUATION_PROGRAM_WORD_CAP = 6472;
constexpr u32 BWD_CONTINUATION_MAX_IMMEDIATES = 512;

static_assert(BWD_COEFF_BANK_CAPACITY * sizeof(e4) == 28 * 1024, "coefficient bank size drift");
static_assert(BWD_COEFF_BANK_CAPACITY <= BWD_COEFF_MAX_COEFFICIENT_ENCODINGS, "coefficient bank encoding overflow");

constexpr u32 BWD_CONTINUATION_WORDS_PER_TERM = 3;
constexpr u32 BWD_CONTINUATION_COEFFICIENT_SHIFT = 0;
constexpr u16 BWD_CONTINUATION_COEFFICIENT_MASK = (1u << BWD_COEFF_HEADER_COEFFICIENT_BITS) - 1;
constexpr u32 BWD_CONTINUATION_CLASS_SHIFT = BWD_COEFF_HEADER_COEFFICIENT_BITS;
constexpr u16 BWD_CONTINUATION_CLASS_MASK = (1u << BWD_COEFF_HEADER_OPCODE_BITS) - 1;
constexpr u16 BWD_PROGRAM_SOURCE_NONE = 0xffff;

constexpr u16 BWD_R0_CLASS_C0_LINEAR_BF = 0;
constexpr u16 BWD_R0_CLASS_C0_LINEAR_E4 = 1;
constexpr u16 BWD_R0_CLASS_C2_PRODUCT_BF_BF = 2;
constexpr u16 BWD_R0_CLASS_C2_PRODUCT_BF_E4 = 3;

constexpr u16 BWD_CONTINUATION_CLASS_C0_LINEAR_E4 = 0;
constexpr u16 BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4 = 1;
constexpr u16 BWD_CONTINUATION_CLASS_GROUP_HEADER = 2;

constexpr u16 BWD_CONTINUATION_GROUP_FLAG_C0 = 1;
constexpr u16 BWD_CONTINUATION_GROUP_FLAG_C2 = 2;
constexpr u16 BWD_PROGRAM_IMMEDIATE_ONE = 0;
constexpr u16 BWD_PROGRAM_IMMEDIATE_NEG_ONE = 1;
constexpr u16 BWD_PROGRAM_IMMEDIATE_RESERVED = 2;

constexpr u32 BWD_FOLD_WEIGHT_SLOTS = 11;
constexpr u32 BWD_FOLD_WEIGHT_BASE_D1 = 0;
constexpr u32 BWD_FOLD_WEIGHT_BASE_D2 = 1;
constexpr u32 BWD_FOLD_WEIGHT_BASE_D3 = 4;

} // namespace airbender::gkr

EXTERN __device__ __constant__ e4 ab_gkr_bwd_coeff_bank[airbender::gkr::BWD_COEFF_BANK_CAPACITY];
#define AB_GKR_BWD_COEFF(slot) (::ab_gkr_bwd_coeff_bank[(slot)])

EXTERN __device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_bwd_fold_weights[airbender::gkr::BWD_FOLD_WEIGHT_SLOTS];

EXTERN __global__ void ab_gkr_bwd_build_fold_weights_kernel(e4 *fold_weights, u32 round);
