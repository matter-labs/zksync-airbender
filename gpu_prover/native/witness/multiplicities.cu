#include "../arg_utils.cuh"
#include "../memory.cuh"
#include "common.cuh"

using namespace ::airbender::arg_utils;
using namespace ::airbender::memory;

namespace airbender::witness::multiplicities {

EXTERN __global__ void ab_generate_multiplicities_kernel(const u32 *const __restrict__ unique_indexes, const u32 *const __restrict__ counts,
                                                         const u32 *const __restrict__ num_runs, const matrix_setter<bf, st_modifier::cs> multiplicities,
                                                         const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  if (gid >= num_runs[0] - 1)
    return;
  const unsigned stride = multiplicities.stride - 1;
  const u32 index = unique_indexes[gid];
  const unsigned row = index % stride;
  const unsigned col = index / stride;
  const bf value = bf::from_u32(counts[gid]);
  multiplicities.set(row, col, value);
}

EXTERN __launch_bounds__(128, 8) __global__ void ab_generate_range_check_lookup_mappings_kernel(
    matrix_getter<bf, ld_modifier::cg> setup_cols, matrix_getter<bf, ld_modifier::cg> witness_cols, matrix_getter<bf, ld_modifier::cg> memory_cols,
    matrix_setter<unsigned, st_modifier::cs> range_check_16_lookup_mapping, matrix_setter<unsigned, st_modifier::cs> timestamp_lookup_mapping,
    __grid_constant__ const RangeCheckArgsLayout explicit_range_check_16_layout, __grid_constant__ const FlattenedLookupExpressionsLayout expressions,
    __grid_constant__ const FlattenedLookupExpressionsForShuffleRamLayout expressions_for_shuffle_ram, const bf memory_timestamp_high_from_circuit_idx,
    const bool process_shuffle_ram_init, const unsigned lazy_init_address_start, const unsigned trace_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid > trace_len)
    return;

  setup_cols.add_row(gid);
  witness_cols.add_row(gid);
  memory_cols.add_row(gid);
  range_check_16_lookup_mapping.add_row(gid);
  timestamp_lookup_mapping.add_row(gid);

  // We can treat contributions in any order, as long as range check 16 and
  // timestamp values end up in the right respective maps.

  for (unsigned i = 0; i < 2 * explicit_range_check_16_layout.num_dst_cols; i++) {
    const unsigned src = i + explicit_range_check_16_layout.src_cols_start;
    const unsigned val = bf::into_canonical_u32(witness_cols.get_at_col(src));
    range_check_16_lookup_mapping.set(val);
    range_check_16_lookup_mapping.add_col(1);
  }

  // Lookup expressions. These don't use setup cols.
  // eval_a_and_b from arg_utils.cuh evaluates 2 expressions at a time because the API was designed for the stage 2 and 3 kernels,
  // Evaluating 2 at a time is not essential here, but not a problem.
  {
    unsigned i{0}, expression_idx{0}, flat_term_idx{0};
    for (; i < expressions.num_range_check_16_expression_pairs; i++) {
      bf a_and_b[2];
      eval_a_and_b<true>(a_and_b, expressions, expression_idx, flat_term_idx, witness_cols, memory_cols, expressions.range_check_16_constant_terms_are_zero);
      range_check_16_lookup_mapping.set(bf::into_canonical_u32(a_and_b[0]));
      range_check_16_lookup_mapping.add_col(1);
      range_check_16_lookup_mapping.set(bf::into_canonical_u32(a_and_b[1]));
      range_check_16_lookup_mapping.add_col(1);
    }

    for (; i < expressions.num_range_check_16_expression_pairs + expressions.num_timestamp_expression_pairs; i++) {
      bf a_and_b[2];
      eval_a_and_b<true>(a_and_b, expressions, expression_idx, flat_term_idx, witness_cols, memory_cols, expressions.timestamp_constant_terms_are_zero);
      timestamp_lookup_mapping.set(bf::into_canonical_u32(a_and_b[0]));
      timestamp_lookup_mapping.add_col(1);
      timestamp_lookup_mapping.set(bf::into_canonical_u32(a_and_b[1]));
      timestamp_lookup_mapping.add_col(1);
    }
  }

  // Lookup expressions for shuffle ram. Unlike the expressions above, these may use setup cols.
  for (unsigned i = 0, expression_idx = 0, flat_term_idx = 0; i < expressions_for_shuffle_ram.num_expression_pairs; i++) {
    bf a_and_b[2];
    eval_a_and_b<true>(a_and_b, expressions_for_shuffle_ram, expression_idx, flat_term_idx, setup_cols, witness_cols, memory_cols);
    a_and_b[1] = bf::sub(a_and_b[1], memory_timestamp_high_from_circuit_idx);
    timestamp_lookup_mapping.set(bf::into_canonical_u32(a_and_b[0]));
    timestamp_lookup_mapping.add_col(1);
    timestamp_lookup_mapping.set(bf::into_canonical_u32(a_and_b[1]));
    timestamp_lookup_mapping.add_col(1);
  }

  if (process_shuffle_ram_init) {
    const bf val0 = memory_cols.get_at_col(lazy_init_address_start);
    const bf val1 = memory_cols.get_at_col(lazy_init_address_start + 1);
    range_check_16_lookup_mapping.set(bf::into_canonical_u32(val0));
    range_check_16_lookup_mapping.add_col(1);
    range_check_16_lookup_mapping.set(bf::into_canonical_u32(val1));
  }
}

} // namespace airbender::witness::multiplicities