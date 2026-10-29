#pragma once
#include "../../forward/fwd_vm.cuh"
#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::forward {
using pr = ::airbender::primitives::field::proth120;
constexpr u32 PR_FWD_VM_BUCKETS = 4;
constexpr u32 PR_FWD_VM_CONST_CAP = 64;
struct fwd_vm_reduction_pair_pr {
  const pr *input[2];
  pr *round_outputs[FWD_VM_FUSED_REDUCTION_ROUNDS][2];
  u32 kind;
  u32 reserved;
};

struct fwd_vm_desc_pr {
  const pr *arg_derived;
  const pr *const_derived;
  char *source_base[FWD_VM_SOURCE_WINDOW_COUNT];
  char *dst_base[FWD_VM_DST_SLOT_COUNT];
  const u32 *mapping_arena[FWD_VM_MAPPING_ARENA_COUNT];
  const pr *table;
  const pr *mask;
  const u32 *decoder_mapping;
  u32 source_stride_bytes[FWD_VM_SOURCE_WINDOW_COUNT];
  u32 dst_stride_bytes[FWD_VM_DST_SLOT_COUNT];
  pr consts[PR_FWD_VM_CONST_CAP];
  u32 table_len;
  u32 descs[FWD_VM_DESC_CAP];
  u32 count;
  u32 layer_count;
  fwd_vm_layer layers[FWD_VM_LAYER_CAP];
  u32 reduction_pair_count;
  fwd_vm_reduction_pair_pr reduction_pairs[FWD_VM_REDUCTION_PAIR_CAP];
  u16 program[FWD_VM_PROGRAM_CAP];
  u32 temporary_source_mask;
  u32 temporary_dst_mask;
};
static_assert(sizeof(fwd_vm_desc_pr) == 28272, "Proth120 forward ABI drift");
static_assert(alignof(fwd_vm_desc_pr) == 16, "Proth120 forward ABI drift");
static_assert(__builtin_offsetof(fwd_vm_desc_pr, consts) == 448, "Proth120 forward ABI drift");
static_assert(__builtin_offsetof(fwd_vm_desc_pr, reduction_pairs) == 3000, "Proth120 forward ABI drift");
static_assert(__builtin_offsetof(fwd_vm_desc_pr, program) == 3680, "Proth120 forward ABI drift");
static_assert(__builtin_offsetof(fwd_vm_desc_pr, temporary_source_mask) == 28256, "Proth120 forward ABI drift");
static_assert(__builtin_offsetof(fwd_vm_desc_pr, temporary_dst_mask) == 28260, "Proth120 forward ABI drift");
static_assert(sizeof(fwd_vm_reduction_pair_pr) == 136, "Proth120 forward ABI drift");
static_assert(sizeof(fwd_vm_desc_pr) <= 32764, "Proth120 forward launch arguments exceed 32764 bytes");
} // namespace airbender::gkr::proth120::forward
