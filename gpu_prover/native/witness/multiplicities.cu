#include "../memory.cuh"
#include "common.cuh"
#include "memory.cuh"

using namespace ::airbender::memory;
using namespace ::airbender::witness::memory;

namespace airbender::witness::multiplicities {

EXTERN __global__ void ab_generate_multiplicities_kernel(const u32 *const __restrict__ unique_indexes, const u32 *const __restrict__ counts,
                                                         const u32 *const __restrict__ num_runs, const matrix_setter<bf, st_modifier::cs> multiplicities,
                                                         const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  if (gid >= num_runs[0])
    return;
  const unsigned stride = multiplicities.stride;
  const u32 index = unique_indexes[gid];
  if (index == 0xffffffffu)
    return;
  const unsigned row = index % stride;
  const unsigned col = index / stride;
  const bf value = bf::from_canonical_u32(counts[gid]);
  multiplicities.set(row, col, value);
}

#define MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT 8

struct LookupExpressions {
  u32 relations_count;
  NoFieldLinearRelation relations[MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT];
};

DEVICE_FORCEINLINE void process_expressions(const matrix_getter<bf, ld_modifier::cg> memory, const matrix_getter<bf, ld_modifier::cg> witness,
                                            const LookupExpressions expressions, matrix_setter<unsigned, st_modifier::cs> mapping) {
#pragma unroll
  for (int i = 0; i < MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT; i++) {
    if (i == expressions.relations_count)
      break;
    const auto relation = expressions.relations[i];
    const bf field_value = evaluate_linear_relation(memory, witness, relation);
    const u32 value = bf::into_canonical_u32(field_value);
    mapping.set(value);
    mapping.add_col(1);
  }
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_generate_range_check_lookup_mapping_kernel(matrix_getter<bf, ld_modifier::cg> memory, matrix_getter<bf, ld_modifier::cg> witness,
                                                       __grid_constant__ const LookupExpressions range_check_16_lookup_expressions,
                                                       matrix_setter<unsigned, st_modifier::cs> range_check_16_lookup_mapping,
                                                       __grid_constant__ const LookupExpressions range_check_timestamp_lookup_expressions,
                                                       matrix_setter<unsigned, st_modifier::cs> range_check_timestamp_lookup_mapping, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  witness.add_row(gid);
  memory.add_row(gid);
  range_check_16_lookup_mapping.add_row(gid);
  range_check_timestamp_lookup_mapping.add_row(gid);
  process_expressions(memory, witness, range_check_16_lookup_expressions, range_check_16_lookup_mapping);
  process_expressions(memory, witness, range_check_timestamp_lookup_expressions, range_check_timestamp_lookup_mapping);
}

} // namespace airbender::witness::multiplicities
