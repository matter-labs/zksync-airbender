#pragma once

#define FUSED_KERNEL_NAME(NAME) ab_generate_fused_##NAME##_kernel
#define FUSED_KERNEL(NAME, ORACLE)                                                                                                                             \
  EXTERN __global__ void FUSED_KERNEL_NAME(NAME)(                                                                                                              \
      const __grid_constant__ DelegationMemoryLayout layout, const __grid_constant__ DelegationAuxLayoutData aux_layout_data,                                  \
      const __grid_constant__ ORACLE oracle, const wrapped_f *const __restrict__ generic_lookup_tables, bf *memory_storage, bf *witness_storage,               \
      wrapped_f *scratch_storage, u32 *const __restrict__ generic_lookup_mapping, const __grid_constant__ LookupExpressions range_check_16_lookup_expressions, \
      u32 *range_check_16_lookup_mapping, const __grid_constant__ LookupExpressions range_check_timestamp_lookup_expressions,                                  \
      u32 *range_check_timestamp_lookup_mapping, const unsigned stride, const unsigned count) {                                                                \
    const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;                                                                                                \
    if (gid >= count)                                                                                                                                          \
      return;                                                                                                                                                  \
    FusedValueTraceAccessor<bf> memory{memory_storage + gid, stride};                                                                                          \
    FusedValueTraceAccessor<bf> witness{witness_storage + gid, stride};                                                                                        \
    {                                                                                                                                                          \
      process_delegation_row<true>(layout, aux_layout_data, oracle, memory, witness, gid);                                                                     \
    }                                                                                                                                                          \
    {                                                                                                                                                          \
      SCRATCH                                                                                                                                                  \
      const MaterializedTraceProvider places{memory, witness};                                                                                                 \
      const WitnessProxy<ORACLE, decltype(places)> p = {oracle, generic_lookup_tables, places, generic_lookup_mapping, scratch, stride, gid};                  \
      FN_CALL(generate)                                                                                                                                        \
    }                                                                                                                                                          \
    {                                                                                                                                                          \
      bf *scratch_row = scratch_storage == nullptr ? nullptr : reinterpret_cast<bf *>(scratch_storage + gid);                                                  \
      FusedMappingTraceAccessor<bf> mapping_memory{memory_storage + gid, stride};                                                                              \
      FusedMappingTraceAccessor<bf> mapping_witness{witness_storage + gid, stride};                                                                            \
      FusedMappingTraceAccessor<bf> mapping_scratch{scratch_row, stride};                                                                                      \
      u32 *range_check_16_row = range_check_16_lookup_expressions.relations_count == 0 ? range_check_16_lookup_mapping : range_check_16_lookup_mapping + gid;  \
      u32 *range_check_timestamp_row =                                                                                                                         \
          range_check_timestamp_lookup_expressions.relations_count == 0 ? range_check_timestamp_lookup_mapping : range_check_timestamp_lookup_mapping + gid;   \
      FusedTraceAccessor<u32, ld_modifier::none, st_modifier::cs> range_check_16_mapping{range_check_16_row, stride};                                          \
      FusedTraceAccessor<u32, ld_modifier::none, st_modifier::cs> range_check_timestamp_mapping{range_check_timestamp_row, stride};                            \
      process_lookup_expressions(mapping_memory, mapping_witness, mapping_scratch, range_check_16_lookup_expressions, range_check_16_mapping);                 \
      process_lookup_expressions(mapping_memory, mapping_witness, mapping_scratch, range_check_timestamp_lookup_expressions, range_check_timestamp_mapping);   \
    }                                                                                                                                                          \
  }

FUSED_KERNEL(NAME, ORACLE)

#undef FUSED_KERNEL
#undef FUSED_KERNEL_NAME
