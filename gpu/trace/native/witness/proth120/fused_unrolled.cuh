#pragma once

using FusedUnrolledOracle = std::conditional_t<std::is_same_v<ORACLE, UnrolledMemoryTrace>, UnrolledMemoryOracle, ORACLE>;

struct FusedArgumentsLayout {
  UnrolledMemoryLayout layout;
  AuxLayoutData aux_layout_data;
  FusedUnrolledOracle oracle;
  const wrapped_f *generic_lookup_tables;
  pr *memory_storage;
  pr *witness_storage;
  wrapped_f *scratch_storage;
  u32 *generic_lookup_mapping;
  u32 *decoder_lookup_mapping;
  Proth120LookupExpressions<15> range_check_16;
  u32 *range_check_16_mapping;
  Proth120LookupExpressions<8> timestamp;
  u32 *timestamp_mapping;
  unsigned stride;
  unsigned count;
};
static_assert(sizeof(FusedArgumentsLayout) <= 32764);

#define FUSED_KERNEL_NAME(NAME) ab_pr_generate_fused_##NAME##_kernel
#define FUSED_RANGE_CHECK_16 Proth120LookupExpressions<15>
#define FUSED_TIMESTAMP Proth120LookupExpressions<8>
#include "../fused_unrolled.cuh"
