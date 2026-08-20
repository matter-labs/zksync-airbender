#include "windowed_r0_abi.cuh"

using namespace airbender::gkr_windowed_bench;

extern "C" void ab_gkr_windowed_r0_abi_probe(r0_abi_layout *layout) {
  *layout = {
      sizeof(r0_window_addr),
      alignof(r0_window_addr),
      __builtin_offsetof(r0_window_addr, base),
      __builtin_offsetof(r0_window_addr, log2_stride),
      __builtin_offsetof(r0_window_addr, origin),
      __builtin_offsetof(r0_window_addr, procedural_kind),
      __builtin_offsetof(r0_window_addr, reserved),
      sizeof(r0_window_eq_sizes),
      alignof(r0_window_eq_sizes),
      __builtin_offsetof(r0_window_eq_sizes, high),
      __builtin_offsetof(r0_window_eq_sizes, low),
      sizeof(r0_vm_desc),
      alignof(r0_vm_desc),
      __builtin_offsetof(r0_vm_desc, window_bases),
      __builtin_offsetof(r0_vm_desc, program),
      __builtin_offsetof(r0_vm_desc, eq_low),
      __builtin_offsetof(r0_vm_desc, partials),
      __builtin_offsetof(r0_vm_desc, log_rows),
      __builtin_offsetof(r0_vm_desc, record_count),
      __builtin_offsetof(r0_vm_desc, source_count),
      __builtin_offsetof(r0_vm_desc, window_count),
      __builtin_offsetof(r0_vm_desc, banked_coefficient_count),
      __builtin_offsetof(r0_vm_desc, c_init),
      __builtin_offsetof(r0_vm_desc, eq_sizes),
      __builtin_offsetof(r0_vm_desc, source_slots),
  };
}
