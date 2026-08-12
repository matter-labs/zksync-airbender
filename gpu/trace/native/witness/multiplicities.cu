#include "common.cuh"
#include "lookup_mapping.cuh"
#include "memory.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::memory;
using namespace ::airbender::trace::witness::memory;

namespace airbender::trace::witness::multiplicities {

EXTERN __global__ void ab_generate_multiplicities_kernel(const u32 *const __restrict__ unique_indexes, const u32 *const __restrict__ counts,
                                                         const u32 *const __restrict__ num_runs, u32 *const __restrict__ lookup_mapping,
                                                         const unsigned lookup_mapping_size, const matrix_setter<bf, st_modifier::cs> multiplicities,
                                                         const unsigned multiplicities_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid < lookup_mapping_size && lookup_mapping[gid] == 0xffffffffu)
    lookup_mapping[gid] = 0;
  if (gid >= multiplicities_size)
    return;
  if (gid >= num_runs[0])
    return;
  const unsigned stride = multiplicities.stride;
  const u32 index = unique_indexes[gid];
  if (index == 0xffffffffu)
    return;
  const unsigned row = index % stride;
  const unsigned col = index / stride;
  const bf value = bf::from_u32_unchecked(counts[gid]);
  multiplicities.set(row, col, value);
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_generate_range_check_lookup_mapping_kernel(matrix_getter<bf, ld_modifier::cg> memory, matrix_getter<bf, ld_modifier::cg> witness,
                                                       matrix_getter<bf, ld_modifier::cg> scratch,
                                                       __grid_constant__ const LookupExpressions range_check_16_lookup_expressions,
                                                       matrix_setter<unsigned, st_modifier::cs> range_check_16_lookup_mapping,
                                                       __grid_constant__ const LookupExpressions range_check_timestamp_lookup_expressions,
                                                       matrix_setter<unsigned, st_modifier::cs> range_check_timestamp_lookup_mapping, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  witness.add_row(gid);
  memory.add_row(gid);
  scratch.add_row(gid);
  range_check_16_lookup_mapping.add_row(gid);
  range_check_timestamp_lookup_mapping.add_row(gid);
  process_lookup_expressions(memory, witness, scratch, range_check_16_lookup_expressions, range_check_16_lookup_mapping);
  process_lookup_expressions(memory, witness, scratch, range_check_timestamp_lookup_expressions, range_check_timestamp_lookup_mapping);
}

} // namespace airbender::trace::witness::multiplicities
