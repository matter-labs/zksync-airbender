#pragma once

#include "../eval_vm_isa.cuh"
#include "../support/kernel_helpers.cuh"

namespace airbender::gkr {

constexpr u32 FWD_VM_PROGRAM_CAP = 12288;
constexpr u32 FWD_VM_CONST_CAP = 64;
constexpr u32 FWD_VM_ARG_DERIVED_E4_CAP = 12;
constexpr u32 FWD_VM_DESC_CAP = 370;
constexpr u32 FWD_VM_CONST_DERIVED_E4_CAP = 8;
constexpr u32 FWD_VM_SOURCE_WINDOW_COUNT = 16;
constexpr u32 FWD_VM_SOURCE_WINDOW_BITS = 4;
constexpr u32 FWD_VM_SOURCE_COLUMN_BITS = 9;
constexpr u32 FWD_VM_SOURCE_COLUMN_SHIFT = FWD_VM_SOURCE_WINDOW_SHIFT + FWD_VM_SOURCE_WINDOW_BITS;
constexpr u32 FWD_VM_SOURCE_WINDOW_MASK = (1u << FWD_VM_SOURCE_WINDOW_BITS) - 1;
constexpr u32 FWD_VM_SOURCE_COLUMN_MASK = (1u << FWD_VM_SOURCE_COLUMN_BITS) - 1;
constexpr u32 FWD_VM_LAYER_CAP = 8;
constexpr u32 FWD_VM_DST_SLOT_COUNT = 16;
constexpr u32 FWD_VM_MAPPING_ARENA_COUNT = 3;
constexpr u32 FWD_VM_FUSED_REDUCTION_ROUNDS = 7;
constexpr u32 FWD_VM_REDUCTION_PAIR_CAP = 5;
constexpr u32 FWD_VM_REDUCTION_PAIR_PAIRWISE2 = 0;
constexpr u32 FWD_VM_REDUCTION_PAIR_LOOKUP = 1;

// The Rust side encodes both the VM's fused-reduction prefix and the dim-reducing tower
// batch with the single vocabulary in vm/desc.rs; pin the two native copies.
static_assert(FWD_VM_REDUCTION_PAIR_CAP == GKR_DIM_REDUCING_FORWARD_TOWER_PAIR_CAP, "reduction-pair cap drift");
static_assert(FWD_VM_REDUCTION_PAIR_PAIRWISE2 == GKR_DIM_REDUCING_FORWARD_TOWER_PAIRWISE2, "reduction-pair kind drift");
static_assert(FWD_VM_REDUCTION_PAIR_LOOKUP == GKR_DIM_REDUCING_FORWARD_TOWER_LOOKUP, "reduction-pair kind drift");

static_assert(FWD_VM_SOURCE_WINDOW_COUNT == 1u << FWD_VM_SOURCE_WINDOW_BITS, "source-window field width drift");
static_assert(FWD_VM_DST_SLOT_COUNT == 1u << FWD_VM_DST_SLOT_BITS, "destination-slot field width drift");

constexpr u32 SD_SINGLE_COLUMN = 0;
constexpr u32 SD_AGGREGATE = 1;
constexpr u32 SD_SETUP = 2;
constexpr u32 SD_DECODER = 3;
constexpr u32 SD_VIRTUAL = 4;
constexpr u32 SD_INITS_TOP_BITS = 5;

constexpr u32 FWD_VM_DESC_KIND_SHIFT = 0;
constexpr u32 FWD_VM_DESC_KIND_MASK = 0x7;
constexpr u32 FWD_VM_DESC_ARENA_SHIFT = 3;
constexpr u32 FWD_VM_DESC_ARENA_MASK = 0x3;
constexpr u32 FWD_VM_DESC_SET_INDEX_SHIFT = 5;
constexpr u32 FWD_VM_DESC_SET_INDEX_MASK = 0xffff;
constexpr u32 FWD_VM_DESC_VKIND_SHIFT = 21;
constexpr u32 FWD_VM_DESC_VKIND_MASK = 0x7;

struct fwd_vm_layer {
  u16 program_offset;
  u16 instruction_count;
};

struct fwd_vm_reduction_pair {
  const e4 *input[2];
  e4 *round_outputs[FWD_VM_FUSED_REDUCTION_ROUNDS][2];
  u32 kind;
  u32 reserved;
};

struct fwd_vm_desc {
  e4 arg_derived_e4[FWD_VM_ARG_DERIVED_E4_CAP];
  char *source_base[FWD_VM_SOURCE_WINDOW_COUNT];
  char *dst_base[FWD_VM_DST_SLOT_COUNT];
  const u32 *mapping_arena[FWD_VM_MAPPING_ARENA_COUNT];
  const e4 *table;
  const bf *mask;
  u32 source_stride_bytes[FWD_VM_SOURCE_WINDOW_COUNT];
  u32 dst_stride_bytes[FWD_VM_DST_SLOT_COUNT];
  bf consts[FWD_VM_CONST_CAP];
  u32 table_len;
  u32 descs[FWD_VM_DESC_CAP];
  u32 count;
  u32 layer_count;
  fwd_vm_layer layers[FWD_VM_LAYER_CAP];
  u32 reduction_pair_count;
  fwd_vm_reduction_pair reduction_pairs[FWD_VM_REDUCTION_PAIR_CAP];
  u16 program[FWD_VM_PROGRAM_CAP];
};

static_assert(sizeof(fwd_vm_layer) == 4, "fwd_vm_layer ABI size drift");
static_assert(sizeof(fwd_vm_reduction_pair) == 136, "fwd_vm_reduction_pair ABI size drift");
static_assert(alignof(fwd_vm_reduction_pair) == 8, "fwd_vm_reduction_pair ABI alignment drift");
static_assert(__builtin_offsetof(fwd_vm_reduction_pair, round_outputs) == 16, "fwd_vm_reduction_pair output offset drift");
static_assert(__builtin_offsetof(fwd_vm_reduction_pair, kind) == 128, "fwd_vm_reduction_pair kind offset drift");
static_assert(sizeof(fwd_vm_desc) == 27664, "fwd_vm_desc ABI size drift");
static_assert(sizeof(fwd_vm_desc) <= 32764, "fwd_vm_desc exceeds the __grid_constant__ parameter limit");
static_assert(alignof(fwd_vm_desc) == 16, "fwd_vm_desc alignment drift");
static_assert(__builtin_offsetof(fwd_vm_desc, reduction_pair_count) == 2396, "fwd_vm_desc reduction count offset drift");
static_assert(__builtin_offsetof(fwd_vm_desc, reduction_pairs) == 2400, "fwd_vm_desc reduction pairs offset drift");
static_assert(__builtin_offsetof(fwd_vm_desc, program) == 3080, "fwd_vm_desc program offset drift");

} // namespace airbender::gkr
