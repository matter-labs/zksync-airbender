#pragma once

using FusedUnrolledOracle = std::conditional_t<std::is_same_v<ORACLE, UnrolledMemoryTrace>, UnrolledMemoryOracle, ORACLE>;

#ifndef FUSED_KERNEL_NAME
#define FUSED_KERNEL_NAME(NAME) ab_generate_fused_##NAME##_kernel
#define FUSED_RANGE_CHECK_16 LookupExpressionsBf
#define FUSED_TIMESTAMP LookupExpressionsBf
#endif
#define FUSED_KERNEL(NAME)                                                                                                                                     \
  EXTERN __global__ void FUSED_KERNEL_NAME(NAME)(                                                                                                              \
      const __grid_constant__ UnrolledMemoryLayout layout, const __grid_constant__ AuxLayoutData aux_layout_data,                                              \
      const __grid_constant__ FusedUnrolledOracle oracle, const wrapped_f *const __restrict__ generic_lookup_tables, witness_value *memory_storage,            \
      witness_value *witness_storage, wrapped_f *scratch_storage, u32 *const __restrict__ generic_lookup_mapping,                                              \
      u32 *const __restrict__ decoder_lookup_mapping, const __grid_constant__ FUSED_RANGE_CHECK_16 range_check_16_lookup_expressions,                          \
      u32 *range_check_16_lookup_mapping, const __grid_constant__ FUSED_TIMESTAMP range_check_timestamp_lookup_expressions,                                    \
      u32 *range_check_timestamp_lookup_mapping, const unsigned stride, const unsigned count) {                                                                \
    const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;                                                                                                \
    if (gid >= count)                                                                                                                                          \
      return;                                                                                                                                                  \
    FusedValueTraceAccessor<witness_value> memory{memory_storage + gid, stride};                                                                               \
    FusedValueTraceAccessor<witness_value> witness{witness_storage + gid, stride};                                                                             \
    NoopUnrolledCapture capture;                                                                                                                               \
    process_machine_state_assuming_preprocessed_decoder<true>(layout, oracle, memory, witness, decoder_lookup_mapping, capture, gid);                          \
    process_shuffle_ram_access_sets<true>(layout, aux_layout_data, oracle, memory, witness, capture, gid);                                                     \
    SCRATCH                                                                                                                                                    \
    const MaterializedTraceProvider places{memory, witness};                                                                                                   \
    const WitnessProxy<FusedUnrolledOracle, decltype(places)> p = {oracle, generic_lookup_tables, places, generic_lookup_mapping, scratch, stride, gid};       \
    FN_CALL(generate)                                                                                                                                          \
    FusedMappingTraceAccessor<witness_value> mapping_memory{memory_storage + gid, stride};                                                                     \
    FusedMappingTraceAccessor<witness_value> mapping_witness{witness_storage + gid, stride};                                                                   \
    FusedMappingTraceAccessor<witness_value> mapping_scratch{reinterpret_cast<witness_value *>(scratch), stride};                                              \
    u32 *range_check_16_row = range_check_16_lookup_expressions.relations_count == 0 ? range_check_16_lookup_mapping : range_check_16_lookup_mapping + gid;    \
    u32 *range_check_timestamp_row =                                                                                                                           \
        range_check_timestamp_lookup_expressions.relations_count == 0 ? range_check_timestamp_lookup_mapping : range_check_timestamp_lookup_mapping + gid;     \
    FusedTraceAccessor<u32, ld_modifier::none, st_modifier::cs> range_check_16_mapping{range_check_16_row, stride};                                            \
    FusedTraceAccessor<u32, ld_modifier::none, st_modifier::cs> range_check_timestamp_mapping{range_check_timestamp_row, stride};                              \
    process_lookup_expressions(mapping_memory, mapping_witness, mapping_scratch, range_check_16_lookup_expressions, range_check_16_mapping);                   \
    process_lookup_expressions(mapping_memory, mapping_witness, mapping_scratch, range_check_timestamp_lookup_expressions, range_check_timestamp_mapping);     \
  }

FUSED_KERNEL(NAME)

#undef FUSED_KERNEL
#undef FUSED_KERNEL_NAME

#undef FUSED_RANGE_CHECK_16
#undef FUSED_TIMESTAMP
