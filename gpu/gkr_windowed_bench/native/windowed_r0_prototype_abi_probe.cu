#include "windowed_r0_prototype_abi.cuh"
#include "windowed_r0_prototype_accumulator.cuh"

using namespace airbender::gkr_windowed_bench;

template <typename Type> constexpr r0_prototype_descriptor_layout_raw ordinary_layout() {
  return {sizeof(Type), alignof(Type), __builtin_offsetof(Type, common), __builtin_offsetof(Type, program)};
}

template <typename Type, typename Ordinary> constexpr r0_prototype_descriptor_layout_raw materialized_layout() {
  return {sizeof(Type), alignof(Type), __builtin_offsetof(Type, ordinary), __builtin_offsetof(Type, ordinary) + __builtin_offsetof(Ordinary, program)};
}

extern "C" void ab_gkr_windowed_r0_prototype_abi_probe(r0_prototype_abi_layout_raw *layout) {
  *layout = {
      sizeof(r0_prototype_common_desc),
      alignof(r0_prototype_common_desc),
      __builtin_offsetof(r0_prototype_common_desc, window_bases),
      __builtin_offsetof(r0_prototype_common_desc, eq_low),
      __builtin_offsetof(r0_prototype_common_desc, partials),
      __builtin_offsetof(r0_prototype_common_desc, log_rows),
      __builtin_offsetof(r0_prototype_common_desc, record_count),
      __builtin_offsetof(r0_prototype_common_desc, bf_record_count),
      __builtin_offsetof(r0_prototype_common_desc, source_slot_count),
      15,
      {
          ordinary_layout<r0_compact_ordinary>(),
          ordinary_layout<r0_split_slot_ordinary>(),
          ordinary_layout<r0_split_direct_ordinary>(),
          ordinary_layout<r0_homogeneous_slot_ordinary>(),
          ordinary_layout<r0_homogeneous_direct_ordinary>(),
          ordinary_layout<r0_grouped_slot_ordinary>(),
          ordinary_layout<r0_grouped_direct_ordinary>(),
          materialized_layout<r0_current_materialized, r0_prototype_ordinary_slot<R0_CURRENT_PROGRAM_CAPACITY, R0_PROTOTYPE_SOURCE_SLOT_CAPACITY>>(),
          materialized_layout<r0_compact_materialized, r0_compact_ordinary>(),
          materialized_layout<r0_split_slot_materialized, r0_split_slot_ordinary>(),
          materialized_layout<r0_split_direct_materialized, r0_split_direct_ordinary>(),
          materialized_layout<r0_homogeneous_slot_materialized, r0_homogeneous_slot_ordinary>(),
          materialized_layout<r0_homogeneous_direct_materialized, r0_homogeneous_direct_ordinary>(),
          materialized_layout<r0_grouped_slot_materialized, r0_grouped_slot_ordinary>(),
          materialized_layout<r0_grouped_direct_materialized, r0_grouped_direct_ordinary>(),
      },
  };
}
