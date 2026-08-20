#pragma once

#include "windowed_r0_abi.cuh"

namespace airbender::gkr_windowed_bench {

constexpr u32 R0_PROTOTYPE_SECTION_WORDS = 16;
constexpr u32 R0_PROTOTYPE_IMMEDIATE_CAPACITY = 512;
constexpr u32 R0_PROTOTYPE_TILE_CAPACITY = 330;
constexpr u32 R0_PROTOTYPE_TILE_SOURCE_CAPACITY = 2618;
constexpr u32 R0_PROTOTYPE_TILE_RECORD_CAPACITY = 1632;
constexpr u32 R0_PROTOTYPE_SOURCE_SLOT_CAPACITY = 1062;

constexpr u32 R0_CURRENT_PROGRAM_CAPACITY = 6528;
constexpr u32 R0_COMPACT_PROGRAM_CAPACITY = 6208;
constexpr u32 R0_SPLIT_PROGRAM_CAPACITY = 6528;
constexpr u32 R0_HOMOGENEOUS_PROGRAM_CAPACITY = 6368;
constexpr u32 R0_GROUPED_PROGRAM_CAPACITY = 7680;

struct alignas(16) r0_prototype_common_desc {
  r0_window_addr window_bases[R0_WINDOW_CAPACITY];
  const e4 *eq_low;
  e4 *partials;
  u32 log_rows;
  u32 record_count;
  u32 bf_record_count;
  u32 source_slot_count;
};

struct r0_prototype_program_meta {
  u32 program_words;
  u32 immediate_count;
  u32 window_count;
  u32 banked_coefficient_count;
  r0_window_eq_sizes eq_sizes;
  u32 sections[R0_PROTOTYPE_SECTION_WORDS];
  u8 program_sha256[32];
};

template <u32 Program, u32 Sources> struct alignas(16) r0_prototype_ordinary_slot {
  r0_prototype_common_desc common;
  r0_prototype_program_meta meta;
  u16 program[Program];
  u16 source_slots[Sources];
};

template <u32 Program> struct alignas(16) r0_prototype_ordinary_direct {
  r0_prototype_common_desc common;
  r0_prototype_program_meta meta;
  u16 program[Program];
};

template <u32 Program, u32 Sources> struct alignas(16) r0_prototype_ordinary_grouped_slot {
  r0_prototype_common_desc common;
  r0_prototype_program_meta meta;
  u16 program[Program];
  u16 source_slots[Sources];
  u32 immediates[R0_PROTOTYPE_IMMEDIATE_CAPACITY];
};

template <u32 Program> struct alignas(16) r0_prototype_ordinary_grouped_direct {
  r0_prototype_common_desc common;
  r0_prototype_program_meta meta;
  u16 program[Program];
  u32 immediates[R0_PROTOTYPE_IMMEDIATE_CAPACITY];
};

struct r0_prototype_tile_header {
  u16 first_record;
  u16 record_count;
  u16 source_offset;
  u16 source_counts;
};

struct r0_prototype_tile_meta {
  u32 tile_count;
  u32 tile_source_count;
  u32 tile_record_count;
  u32 capacity;
  u32 max_dynamic_shared_bytes;
  u32 reserved[3];
  u8 tile_sha256[32];
};

template <typename Ordinary> struct alignas(16) r0_prototype_materialized {
  Ordinary ordinary;
  r0_prototype_tile_meta tile_meta;
  r0_prototype_tile_header tiles[R0_PROTOTYPE_TILE_CAPACITY];
  u16 tile_sources[R0_PROTOTYPE_TILE_SOURCE_CAPACITY];
  u8 record_local_sources[R0_PROTOTYPE_TILE_RECORD_CAPACITY][2];
};

using r0_compact_ordinary = r0_prototype_ordinary_slot<R0_COMPACT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY>;
using r0_split_slot_ordinary = r0_prototype_ordinary_slot<R0_SPLIT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY>;
using r0_split_direct_ordinary = r0_prototype_ordinary_direct<R0_SPLIT_PROGRAM_CAPACITY>;
using r0_homogeneous_slot_ordinary = r0_prototype_ordinary_slot<R0_HOMOGENEOUS_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY>;
using r0_homogeneous_direct_ordinary = r0_prototype_ordinary_direct<R0_HOMOGENEOUS_PROGRAM_CAPACITY>;
using r0_grouped_slot_ordinary = r0_prototype_ordinary_grouped_slot<R0_GROUPED_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY>;
using r0_grouped_direct_ordinary = r0_prototype_ordinary_grouped_direct<R0_GROUPED_PROGRAM_CAPACITY>;

using r0_current_materialized = r0_prototype_materialized<r0_prototype_ordinary_slot<R0_CURRENT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY>>;
using r0_compact_materialized = r0_prototype_materialized<r0_compact_ordinary>;
using r0_split_slot_materialized = r0_prototype_materialized<r0_split_slot_ordinary>;
using r0_split_direct_materialized = r0_prototype_materialized<r0_split_direct_ordinary>;
using r0_homogeneous_slot_materialized = r0_prototype_materialized<r0_homogeneous_slot_ordinary>;
using r0_homogeneous_direct_materialized = r0_prototype_materialized<r0_homogeneous_direct_ordinary>;
using r0_grouped_slot_materialized = r0_prototype_materialized<r0_grouped_slot_ordinary>;
using r0_grouped_direct_materialized = r0_prototype_materialized<r0_grouped_direct_ordinary>;

struct r0_prototype_descriptor_layout_raw {
  u64 size;
  u64 align;
  u64 common_offset;
  u64 program_offset;
};

struct r0_prototype_abi_layout_raw {
  u64 common_size;
  u64 common_align;
  u64 common_window_bases;
  u64 common_eq_low;
  u64 common_partials;
  u64 common_log_rows;
  u64 common_record_count;
  u64 common_bf_record_count;
  u64 common_source_slot_count;
  u64 descriptor_count;
  r0_prototype_descriptor_layout_raw descriptors[15];
};

static_assert(sizeof(r0_prototype_common_desc) == 1056);
static_assert(alignof(r0_prototype_common_desc) == 16);
static_assert(sizeof(r0_prototype_tile_header) == 8);
static_assert(sizeof(r0_prototype_tile_meta) == 64);

#define R0_PROTOTYPE_ASSERT_FITS(Type) static_assert(sizeof(Type) <= R0_KERNEL_ARGUMENT_CEILING_BYTES)
R0_PROTOTYPE_ASSERT_FITS(r0_compact_ordinary);
R0_PROTOTYPE_ASSERT_FITS(r0_split_slot_ordinary);
R0_PROTOTYPE_ASSERT_FITS(r0_split_direct_ordinary);
R0_PROTOTYPE_ASSERT_FITS(r0_homogeneous_slot_ordinary);
R0_PROTOTYPE_ASSERT_FITS(r0_homogeneous_direct_ordinary);
R0_PROTOTYPE_ASSERT_FITS(r0_grouped_slot_ordinary);
R0_PROTOTYPE_ASSERT_FITS(r0_grouped_direct_ordinary);
R0_PROTOTYPE_ASSERT_FITS(r0_current_materialized);
R0_PROTOTYPE_ASSERT_FITS(r0_compact_materialized);
R0_PROTOTYPE_ASSERT_FITS(r0_split_slot_materialized);
R0_PROTOTYPE_ASSERT_FITS(r0_split_direct_materialized);
R0_PROTOTYPE_ASSERT_FITS(r0_homogeneous_slot_materialized);
R0_PROTOTYPE_ASSERT_FITS(r0_homogeneous_direct_materialized);
R0_PROTOTYPE_ASSERT_FITS(r0_grouped_slot_materialized);
R0_PROTOTYPE_ASSERT_FITS(r0_grouped_direct_materialized);
#undef R0_PROTOTYPE_ASSERT_FITS

} // namespace airbender::gkr_windowed_bench
