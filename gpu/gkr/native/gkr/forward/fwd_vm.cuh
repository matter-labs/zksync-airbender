#pragma once

#include "gkr/eval_vm_isa.cuh"
#include "gkr/support/kernel_helpers.cuh"

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

static_assert(sizeof(fwd_vm_layer) == 4, "fwd_vm_layer ABI size drift");

} // namespace airbender::gkr
