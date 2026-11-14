#pragma once
#include "fwd_vm.cuh"
namespace airbender::gkr::forward_vm_detail {
struct fwd_vm_special {
  u32 kind;
  u32 arena;
  u32 set_index;
  u32 vkind;
};
template <typename Desc> DEVICE_FORCEINLINE const char *source_col(const Desc &d, const u32 window, const u32 col) {
  return d.source_base[window] + static_cast<size_t>(col) * d.source_stride_bytes[window];
}
template <typename Desc> DEVICE_FORCEINLINE char *dst_col(const Desc &d, const u32 slot, const u32 col) {
  return d.dst_base[slot] + static_cast<size_t>(col) * d.dst_stride_bytes[slot];
}
DEVICE_FORCEINLINE fwd_vm_special unpack_special(const u32 w) {
  fwd_vm_special s;
  s.kind = (w >> FWD_VM_DESC_KIND_SHIFT) & FWD_VM_DESC_KIND_MASK;
  s.arena = (w >> FWD_VM_DESC_ARENA_SHIFT) & FWD_VM_DESC_ARENA_MASK;
  s.set_index = (w >> FWD_VM_DESC_SET_INDEX_SHIFT) & FWD_VM_DESC_SET_INDEX_MASK;
  s.vkind = (w >> FWD_VM_DESC_VKIND_SHIFT) & FWD_VM_DESC_VKIND_MASK;
  return s;
}
// Mapping = one column of a contiguous u32 arena (column-major, stride = count).
template <typename Desc> DEVICE_FORCEINLINE const u32 *special_mapping(const Desc &d, const fwd_vm_special &s) {
  return d.mapping_arena[s.arena] + static_cast<size_t>(s.set_index) * d.count;
}
} // namespace airbender::gkr::forward_vm_detail
