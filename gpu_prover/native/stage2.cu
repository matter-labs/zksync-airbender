#include "arg_utils.cuh"
#include "ops_complex.cuh"
#include "vectorized.cuh"

using namespace ::airbender::arg_utils;
using namespace ::airbender::field;
using namespace ::airbender::memory;
using namespace ::airbender::ops_complex;
using namespace ::airbender::vectorized;

namespace airbender::stage2 {

using bf = base_field;
using e2 = ext2_field;
using e4 = ext4_field;

// Populates entry-invs and b-cols.
// ENTRY_WIDTH = 1 instantiation computes aggregated entries and multiplicity args for range check 16 lookups.
// ENTRY_WIDTH = 4 instantiation computes aggregated entries and multiplicity args for generic lookups.
template <unsigned ENTRY_WIDTH>
DEVICE_FORCEINLINE void
aggregated_entry_invs_and_multiplicities_arg_kernel(const LookupChallenges *challenges_ptr, matrix_getter<bf, ld_modifier::cs> witness_cols,
                                                    matrix_getter<bf, ld_modifier::cs> setup_cols, vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols,
                                                    // st_modifier::cg to cache stores for upcoming lookup_a_args_kernel
                                                    vector_setter<e4, st_modifier::cg> aggregated_entry_invs, const unsigned start_col_in_setup,
                                                    const unsigned multiplicities_src_cols_start, const unsigned multiplicities_dst_cols_start,
                                                    const unsigned num_multiplicities_cols, const unsigned num_table_rows_tail, const unsigned log_n) {
  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  // Zeroing the last row for stage 2 bf and e4 args is handled by lookup_args_kernel.
  if (gid >= n - 1)
    return;

  stage_2_e4_cols.add_row(gid);
  stage_2_e4_cols.add_col(multiplicities_dst_cols_start);
  witness_cols.add_row(gid);
  witness_cols.add_col(multiplicities_src_cols_start);
  aggregated_entry_invs += gid;

  // for width = 1 (range check) the value is the row index. We can just use gid instead of reading from setup.
  if (ENTRY_WIDTH > 1) {
    setup_cols.add_row(gid);
    setup_cols.add_col(start_col_in_setup);
  }

  const auto [linearization_challenges, gamma] = *challenges_ptr;
  for (unsigned i = 0; i < num_multiplicities_cols; i++) {
    if (i == num_multiplicities_cols - 1 && gid >= num_table_rows_tail) {
      stage_2_e4_cols.set(e4::zero());
      return;
    }

    // for range checks, we can just use gid
    bf val;
    if (ENTRY_WIDTH == 1) {
      val = bf{gid};
    } else {
      val = setup_cols.get();
      setup_cols.add_col(1);
    }
    e4 denom = e4::add(gamma, val);
    if (ENTRY_WIDTH > 1) { // hint to compiler to optimize this part out if possible
#pragma unroll
      for (unsigned j = 1; j < ENTRY_WIDTH; j++) {
        const auto val = setup_cols.get();
        setup_cols.add_col(1);
        denom = e4::add(denom, e4::mul(linearization_challenges[j - 1], val));
      }
    }

    const e4 denom_inv{e4::inv(denom)};

    const auto multiplicity = witness_cols.get();
    stage_2_e4_cols.set(e4::mul(denom_inv, multiplicity));
    aggregated_entry_invs.set(denom_inv);

    witness_cols.add_col(1);
    aggregated_entry_invs += n - 1; // next iteration's warp accesses will be unaligned, but this is likely negligible overall
    stage_2_e4_cols.add_col(1);
  }
}

// TODO (optional): I could unify
// range_check_aggregated_entry_invs_and_multiplicities_arg_kernel
// and
// generic_aggregated_entry_invs_and_multiplicities_arg_kernel
// into a one-size-fits-all kernel by making ENTRY_WIDTH a runtime argument instead of a template parameter.
// I think they're alright as-is.
EXTERN __launch_bounds__(128, 8) __global__ void ab_range_check_aggregated_entry_invs_and_multiplicities_arg_kernel(
    const LookupChallenges *challenges, matrix_getter<bf, ld_modifier::cs> witness_cols, matrix_getter<bf, ld_modifier::cs> setup_cols,
    vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols,
    // st_modifier::cg to cache stores for upcoming lookup_a_args_kernel
    vector_setter<e4, st_modifier::cg> aggregated_entry_invs, const unsigned start_col_in_setup, const unsigned multiplicities_src_cols_start,
    const unsigned multiplicities_dst_cols_start, const unsigned num_multiplicities_cols, const unsigned num_table_rows_tail, const unsigned log_n) {

  aggregated_entry_invs_and_multiplicities_arg_kernel<1>(challenges, witness_cols, setup_cols, stage_2_e4_cols, aggregated_entry_invs, start_col_in_setup,
                                                         multiplicities_src_cols_start, multiplicities_dst_cols_start, num_multiplicities_cols,
                                                         num_table_rows_tail, log_n);
}

EXTERN __launch_bounds__(128, 8) __global__ void ab_generic_aggregated_entry_invs_and_multiplicities_arg_kernel(
    const LookupChallenges *challenges, matrix_getter<bf, ld_modifier::cs> witness_cols, matrix_getter<bf, ld_modifier::cs> setup_cols,
    vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols,
    // st_modifier::cg to cache stores for upcoming lookup_a_args_kernel
    vector_setter<e4, st_modifier::cg> aggregated_entry_invs, const unsigned start_col_in_setup, const unsigned multiplicities_src_cols_start,
    const unsigned multiplicities_dst_cols_start, const unsigned num_multiplicities_cols, const unsigned num_table_rows_tail, const unsigned log_n) {
  aggregated_entry_invs_and_multiplicities_arg_kernel<NUM_LOOKUP_ARGUMENT_KEY_PARTS>(
      challenges, witness_cols, setup_cols, stage_2_e4_cols, aggregated_entry_invs, start_col_in_setup, multiplicities_src_cols_start,
      multiplicities_dst_cols_start, num_multiplicities_cols, num_table_rows_tail, log_n);
}

// This kernel is just for one arg col and should be negligible.
// I'm making it standalone because it doesn't quite fit with the others and
// for easier comparison to zksync_airbender's stage2.rs control flow.
EXTERN __launch_bounds__(128, 8) __global__
    void ab_delegation_aux_poly_kernel(__grid_constant__ const DelegationChallenges challenges,
                                       __grid_constant__ const DelegationRequestMetadata request_metadata,
                                       __grid_constant__ const DelegationProcessingMetadata processing_metadata, matrix_getter<bf, ld_modifier::cs> memory_cols,
                                       matrix_getter<bf, ld_modifier::cs> setup_cols, vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols,
                                       const unsigned delegation_aux_poly_col, const bool handle_delegation_requests, const unsigned log_n) {
  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  // Zeroing the last row for stage 2 bf and e4 args is handled by lookup_args_kernel.
  if (gid >= n - 1)
    return;

  stage_2_e4_cols.add_row(gid);
  memory_cols.add_row(gid);
  setup_cols.add_row(gid);

  if (handle_delegation_requests) {
    const bf num = memory_cols.get_at_col(request_metadata.multiplicity_col);

    bf timestamp_low = setup_cols.get_at_col(request_metadata.timestamp_setup_col);
    timestamp_low = bf::add(timestamp_low, request_metadata.in_cycle_write_idx);

    bf timestamp_high = setup_cols.get_at_col(request_metadata.timestamp_setup_col + 1);
    timestamp_high = bf::add(timestamp_high, request_metadata.memory_timestamp_high_from_circuit_idx);

    e4 denom = challenges.gamma;
    denom = e4::add(denom, memory_cols.get_at_col(request_metadata.delegation_type_col));
    denom = e4::add(denom, e4::mul(challenges.linearization_challenges[0], memory_cols.get_at_col(request_metadata.abi_mem_offset_high_col)));
    denom = e4::add(denom, e4::mul(challenges.linearization_challenges[1], timestamp_low));
    denom = e4::add(denom, e4::mul(challenges.linearization_challenges[2], timestamp_high));

    const e4 denom_inv{e4::inv(denom)};
    stage_2_e4_cols.set_at_col(delegation_aux_poly_col, e4::mul(num, denom_inv));
  } else /* process_delegations */ {
    const bf num = memory_cols.get_at_col(processing_metadata.multiplicity_col);

    e4 denom = challenges.gamma;
    denom = e4::add(denom, processing_metadata.delegation_type);
    denom = e4::add(denom, e4::mul(challenges.linearization_challenges[0], memory_cols.get_at_col(processing_metadata.abi_mem_offset_high_col)));
    denom = e4::add(denom, e4::mul(challenges.linearization_challenges[1], memory_cols.get_at_col(processing_metadata.write_timestamp_col)));
    denom = e4::add(denom, e4::mul(challenges.linearization_challenges[2], memory_cols.get_at_col(processing_metadata.write_timestamp_col + 1)));

    const e4 denom_inv{e4::inv(denom)};
    stage_2_e4_cols.set_at_col(delegation_aux_poly_col, e4::mul(num, denom_inv));
  }
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_lookup_args_kernel(__grid_constant__ const RangeCheckArgsLayout range_check_16_layout,
                               __grid_constant__ const FlattenedLookupExpressionsLayout expressions,
                               __grid_constant__ const FlattenedLookupExpressionsForShuffleRamLayout expressions_for_shuffle_ram,
                               __grid_constant__ const LazyInitTeardownLayout lazy_init_teardown_layout, matrix_getter<bf, ld_modifier::cs> setup_cols,
                               matrix_getter<bf, ld_modifier::cs> witness_cols, matrix_getter<bf, ld_modifier::cs> memory_cols,
                               vector_getter<e4, ld_modifier::ca> aggregated_entry_invs_for_range_check_16,
                               vector_getter<e4, ld_modifier::ca> aggregated_entry_invs_for_timestamp_range_checks,
                               vector_getter<e4, ld_modifier::ca> aggregated_entry_invs_for_generic_lookups, const unsigned generic_args_start,
                               const unsigned num_generic_args, matrix_getter<unsigned, ld_modifier::cs> generic_lookups_args_to_table_entries_map,
                               matrix_setter<bf, st_modifier::cs> stage_2_bf_cols, vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols,
                               const bf memory_timestamp_high_from_circuit_idx, const unsigned num_stage_2_bf_cols, const unsigned num_stage_2_e4_cols,
                               const unsigned log_n) {
  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= n)
    return;

  stage_2_bf_cols.add_row(gid);
  stage_2_e4_cols.add_row(gid);

  // For bf cols, the final row is reserved for c0 = 0 adjustments.
  // Here we take the opportunity to zero the final row for all stage 2 arg cols.
  if (gid == n - 1) {
    for (unsigned i = 0; i < num_stage_2_bf_cols; i++)
      stage_2_bf_cols.set_at_col(i, bf::zero());
    for (unsigned i = 0; i < num_stage_2_e4_cols; i++)
      stage_2_e4_cols.set_at_col(i, e4::zero());
    return;
  }

  setup_cols.add_row(gid);
  witness_cols.add_row(gid);
  memory_cols.add_row(gid);
  generic_lookups_args_to_table_entries_map.add_row(gid);

  // aggregated_entry_invs loads are uncoalesced e4, but should hit in L2 (or L1 if we're lucky)

  // range check 16 args
  for (unsigned i = 0; i < range_check_16_layout.num_dst_cols; i++) {
    const unsigned src = 2 * i + range_check_16_layout.src_cols_start;
    const bf val0 = bf::into_canonical(witness_cols.get_at_col(src));
    const bf val1 = bf::into_canonical(witness_cols.get_at_col(src + 1));
    const auto entry0 = aggregated_entry_invs_for_range_check_16.get(val0.limb);
    const auto entry1 = aggregated_entry_invs_for_range_check_16.get(val1.limb);
    const auto bf_arg = bf::mul(val0, val1);
    const auto e4_arg = e4::add(entry0, entry1);
    stage_2_bf_cols.set_at_col(range_check_16_layout.bf_args_start + i, bf_arg);
    stage_2_e4_cols.set_at_col(range_check_16_layout.e4_args_start + i, e4_arg);
  }

  // Lookup expressions. These don't use setup cols.
  {
    unsigned i{0}, expression_idx{0}, flat_term_idx{0};
    for (; i < expressions.num_range_check_16_expression_pairs; i++) {
      bf a_and_b[2];
      eval_a_and_b<true>(a_and_b, expressions, expression_idx, flat_term_idx, witness_cols, memory_cols, expressions.range_check_16_constant_terms_are_zero);
      a_and_b[0] = bf::into_canonical(a_and_b[0]);
      a_and_b[1] = bf::into_canonical(a_and_b[1]);
      const e4 entry_a = aggregated_entry_invs_for_range_check_16.get(a_and_b[0].limb);
      const e4 entry_b = aggregated_entry_invs_for_range_check_16.get(a_and_b[1].limb);
      const bf bf_arg = bf::mul(a_and_b[0], a_and_b[1]);
      const e4 e4_arg = e4::add(entry_a, entry_b);
      stage_2_bf_cols.set_at_col(expressions.bf_dst_cols[i], bf_arg);
      stage_2_e4_cols.set_at_col(expressions.e4_dst_cols[i], e4_arg);
    }

    for (; i < expressions.num_range_check_16_expression_pairs + expressions.num_timestamp_expression_pairs; i++) {
      bf a_and_b[2];
      eval_a_and_b<true>(a_and_b, expressions, expression_idx, flat_term_idx, witness_cols, memory_cols, expressions.timestamp_constant_terms_are_zero);
      a_and_b[0] = bf::into_canonical(a_and_b[0]);
      a_and_b[1] = bf::into_canonical(a_and_b[1]);
      const e4 entry_a = aggregated_entry_invs_for_timestamp_range_checks.get(a_and_b[0].limb);
      const e4 entry_b = aggregated_entry_invs_for_timestamp_range_checks.get(a_and_b[1].limb);
      const bf bf_arg = bf::mul(a_and_b[0], a_and_b[1]);
      const e4 e4_arg = e4::add(entry_a, entry_b);
      stage_2_bf_cols.set_at_col(expressions.bf_dst_cols[i], bf_arg);
      stage_2_e4_cols.set_at_col(expressions.e4_dst_cols[i], e4_arg);
    }
  }

  // Lookup expressions for shuffle ram. Unlike the expressions above, these may use setup cols.
  for (unsigned i = 0, expression_idx = 0, flat_term_idx = 0; i < expressions_for_shuffle_ram.num_expression_pairs; i++) {
    bf a_and_b[2];
    eval_a_and_b<true>(a_and_b, expressions_for_shuffle_ram, expression_idx, flat_term_idx, setup_cols, witness_cols, memory_cols);
    a_and_b[1] = bf::sub(a_and_b[1], memory_timestamp_high_from_circuit_idx);
    a_and_b[0] = bf::into_canonical(a_and_b[0]);
    a_and_b[1] = bf::into_canonical(a_and_b[1]);
    const e4 entry_a = aggregated_entry_invs_for_timestamp_range_checks.get(a_and_b[0].limb);
    const e4 entry_b = aggregated_entry_invs_for_timestamp_range_checks.get(a_and_b[1].limb);
    const bf bf_arg = bf::mul(a_and_b[0], a_and_b[1]);
    const e4 e4_arg = e4::add(entry_a, entry_b);
    stage_2_bf_cols.set_at_col(expressions_for_shuffle_ram.bf_dst_cols[i], bf_arg);
    stage_2_e4_cols.set_at_col(expressions_for_shuffle_ram.e4_dst_cols[i], e4_arg);
  }

  // 32-bit lazy init address cols, treated as an extra pair of range check 16 cols
  if (lazy_init_teardown_layout.process_shuffle_ram_init) {
    const bf val0 = bf::into_canonical(memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start));
    const bf val1 = bf::into_canonical(memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start + 1));
    const auto entry0 = aggregated_entry_invs_for_range_check_16.get(val0.limb);
    const auto entry1 = aggregated_entry_invs_for_range_check_16.get(val1.limb);
    const auto bf_arg = bf::mul(val0, val1);
    const auto e4_arg = e4::add(entry0, entry1);
    stage_2_bf_cols.set_at_col(lazy_init_teardown_layout.bf_arg_col, bf_arg);
    stage_2_e4_cols.set_at_col(lazy_init_teardown_layout.e4_arg_col, e4_arg);
  }

  // width-3 generic args with fixed table ids. The map makes this simple.
  for (unsigned i = 0; i < num_generic_args; i++) {
    const unsigned absolute_row_index = generic_lookups_args_to_table_entries_map.get_at_col(i);
    const e4 aggregated_entry_inv = aggregated_entry_invs_for_generic_lookups.get(absolute_row_index);
    stage_2_e4_cols.set_at_col(generic_args_start + i, aggregated_entry_inv);
  }
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_shuffle_ram_memory_args_kernel(__grid_constant__ const MemoryChallenges challenges, __grid_constant__ const ShuffleRamAccesses shuffle_ram_accesses,
                                           matrix_getter<bf, ld_modifier::cs> setup_cols, matrix_getter<bf, ld_modifier::cs> memory_cols,
                                           vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols,
                                           __grid_constant__ const LazyInitTeardownLayout lazy_init_teardown_layout,
                                           const bf memory_timestamp_high_from_circuit_idx, const unsigned memory_args_start, const unsigned log_n) {
  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  // Zeroing the last row for stage 2 bf and e4 args is handled by lookup_args_kernel.
  if (gid >= n - 1)
    return;

  stage_2_e4_cols.add_row(gid);
  setup_cols.add_row(gid);
  memory_cols.add_row(gid);

  // TODO:There's a fair number of e4 x e4 muls and e4 invs here.
  // In theory muls of composite terms could be manually unrolled,
  // helped by precomputed cross-term challenge combinations.
  // It's hard to say what level of unrolling would be optimal.

  // Shuffle ram init
  e4 numerator{challenges.gamma};
  const bf address_low = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start);
  numerator = e4::add(numerator, e4::mul(challenges.address_low_challenge, address_low));
  const bf address_high = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start + 1);
  numerator = e4::add(numerator, e4::mul(challenges.address_high_challenge, address_high));

  e4 denom{numerator};
  const bf value_low = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_value_start);
  denom = e4::add(denom, e4::mul(challenges.value_low_challenge, value_low));
  const bf value_high = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_value_start + 1);
  denom = e4::add(denom, e4::mul(challenges.value_high_challenge, value_high));
  const bf timestamp_low = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_timestamp_start);
  denom = e4::add(denom, e4::mul(challenges.timestamp_low_challenge, timestamp_low));
  const bf timestamp_high = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_timestamp_start + 1);
  denom = e4::add(denom, e4::mul(challenges.timestamp_high_challenge, timestamp_high));

  // flush result
  e4 num_over_denom_acc = numerator;
  e4 denom_inv{e4::inv(denom)};
  num_over_denom_acc = e4::mul(num_over_denom_acc, denom_inv);
  stage_2_e4_cols.set_at_col(memory_args_start, num_over_denom_acc);

  // Shuffle ram accesses
  // first, read a couple values common across accesses:
  const bf write_timestamp_in_setup_low = setup_cols.get_at_col(shuffle_ram_accesses.write_timestamp_in_setup_start);
  const bf write_timestamp_in_setup_high = setup_cols.get_at_col(shuffle_ram_accesses.write_timestamp_in_setup_start + 1);
#pragma unroll 1
  for (unsigned i = 0; i < shuffle_ram_accesses.num_accesses; i++) {
    const auto &access = shuffle_ram_accesses.accesses[i];

    e4 numerator{challenges.gamma};
    const bf address_low = memory_cols.get_at_col(access.address_start);
    numerator = e4::add(numerator, e4::mul(challenges.address_low_challenge, address_low));

    if (access.is_register_only) {
      numerator = e4::add(numerator, bf::one());
    } else {
      const bf address_high = memory_cols.get_at_col(access.address_start + 1);
      numerator = e4::add(numerator, e4::mul(challenges.address_high_challenge, address_high));
      numerator = e4::add(numerator, memory_cols.get_at_col(access.maybe_is_register_start));
      // TODO: It's possible address_high is always zero when memory_cols.get_at_col(access.maybe_is_register_start) is 1, which suggests:
      // const bf is_reg = memory_cols.get_at_col(access.maybe_is_register_start);
      // numerator = e4::add(numerator, memory_cols.get_at_col(access.maybe_is_register_start));
      // if (is_reg.limb) {
      //   const bf address_high = memory_cols.get_at_col(access.address_start + 1);
      //   numerator = e4::add(numerator, e4::mul(challenges.address_high_challenge, address_high));
      // }
    }

    e4 denom{};

    if (access.is_write) {
      denom = numerator;

      const bf read_value_low = memory_cols.get_at_col(access.read_value_start);
      denom = e4::add(denom, e4::mul(challenges.value_low_challenge, read_value_low));
      const bf read_value_high = memory_cols.get_at_col(access.read_value_start + 1);
      denom = e4::add(denom, e4::mul(challenges.value_high_challenge, read_value_high));

      const bf write_value_low = memory_cols.get_at_col(access.maybe_write_value_start);
      numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, write_value_low));
      const bf write_value_high = memory_cols.get_at_col(access.maybe_write_value_start + 1);
      numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, write_value_high));
    } else {
      const bf value_low = memory_cols.get_at_col(access.read_value_start);
      numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, value_low));
      const bf value_high = memory_cols.get_at_col(access.read_value_start + 1);
      numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, value_high));

      denom = numerator;
    }

    const bf read_timestamp_low = memory_cols.get_at_col(access.read_timestamp_start);
    denom = e4::add(denom, e4::mul(challenges.timestamp_low_challenge, read_timestamp_low));
    const bf read_timestamp_high = memory_cols.get_at_col(access.read_timestamp_start + 1);
    denom = e4::add(denom, e4::mul(challenges.timestamp_high_challenge, read_timestamp_high));

    const bf access_index{i};
    const bf write_timestamp_low = bf::add(write_timestamp_in_setup_low, access_index);
    numerator = e4::add(numerator, e4::mul(challenges.timestamp_low_challenge, write_timestamp_low));
    const bf write_timestamp_high = bf::add(write_timestamp_in_setup_high, memory_timestamp_high_from_circuit_idx);
    numerator = e4::add(numerator, e4::mul(challenges.timestamp_high_challenge, write_timestamp_high));

    // flush result
    num_over_denom_acc = e4::mul(num_over_denom_acc, numerator);
    e4 denom_inv{e4::inv(denom)};
    num_over_denom_acc = e4::mul(num_over_denom_acc, denom_inv);
    stage_2_e4_cols.set_at_col(memory_args_start + 1 + i, num_over_denom_acc);
  }
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_batched_ram_memory_args_kernel(__grid_constant__ const MemoryChallenges challenges, __grid_constant__ const BatchedRamAccesses batched_ram_accesses,
                                           matrix_getter<bf, ld_modifier::cs> memory_cols, vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols,
                                           const unsigned memory_args_start, const unsigned log_n) {
  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  // Zeroing the last row for stage 2 bf and e4 args is handled by lookup_args_kernel.
  if (gid >= n - 1)
    return;

  stage_2_e4_cols.add_row(gid);
  memory_cols.add_row(gid);

  // Batched ram accesses
  // Compute address_high_contribution, which is common across accesses
  const bf address_high = memory_cols.get_at_col(batched_ram_accesses.abi_mem_offset_high_col);
  const e4 address_high_contribution = e4::mul(address_high, challenges.address_high_challenge);
  // Compute write_timestamp_contribution, also common across accesses
  const bf write_timestamp_low = memory_cols.get_at_col(batched_ram_accesses.write_timestamp_col);
  const e4 write_timestamp_low_contribution = e4::mul(write_timestamp_low, challenges.timestamp_low_challenge);
  const bf write_timestamp_high = memory_cols.get_at_col(batched_ram_accesses.write_timestamp_col + 1);
  const e4 write_timestamp_high_contribution = e4::mul(write_timestamp_high, challenges.timestamp_high_challenge);
  const e4 write_timestamp_contribution = e4::add(write_timestamp_low_contribution, write_timestamp_high_contribution);

  e4 num_over_denom_acc{};
#pragma unroll 1
  for (unsigned i = 0; i < batched_ram_accesses.num_accesses; i++) {
    const auto &access = batched_ram_accesses.accesses[i];
    e4 numerator = e4::add(access.gamma_plus_address_low_contribution, address_high_contribution);

    e4 denom{};

    if (access.is_write) {
      denom = numerator;

      const bf read_value_low = memory_cols.get_at_col(access.read_value_col);
      denom = e4::add(denom, e4::mul(challenges.value_low_challenge, read_value_low));
      const bf read_value_high = memory_cols.get_at_col(access.read_value_col + 1);
      denom = e4::add(denom, e4::mul(challenges.value_high_challenge, read_value_high));

      const bf write_value_low = memory_cols.get_at_col(access.maybe_write_value_col);
      numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, write_value_low));
      const bf write_value_high = memory_cols.get_at_col(access.maybe_write_value_col + 1);
      numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, write_value_high));
    } else {
      const bf value_low = memory_cols.get_at_col(access.read_value_col);
      numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, value_low));
      const bf value_high = memory_cols.get_at_col(access.read_value_col + 1);
      numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, value_high));

      denom = numerator;
    }

    numerator = e4::add(numerator, write_timestamp_contribution);

    const bf read_timestamp_low = memory_cols.get_at_col(access.read_timestamp_col);
    denom = e4::add(denom, e4::mul(challenges.timestamp_low_challenge, read_timestamp_low));
    const bf read_timestamp_high = memory_cols.get_at_col(access.read_timestamp_col + 1);
    denom = e4::add(denom, e4::mul(challenges.timestamp_high_challenge, read_timestamp_high));

    // flush result
    if (i == 0)
      num_over_denom_acc = numerator;
    else
      num_over_denom_acc = e4::mul(num_over_denom_acc, numerator);
    e4 denom_inv{e4::inv(denom)};
    num_over_denom_acc = e4::mul(num_over_denom_acc, denom_inv);
    stage_2_e4_cols.set_at_col(memory_args_start + i, num_over_denom_acc);
  }
}

EXTERN __launch_bounds__(128, 8) __global__
    void ab_register_and_indirect_memory_args_kernel(__grid_constant__ const MemoryChallenges challenges,
                                                     __grid_constant__ const RegisterAndIndirectAccesses register_and_indirect_accesses,
                                                     matrix_getter<bf, ld_modifier::cs> memory_cols,
                                                     vectorized_e4_matrix_setter<st_modifier::cs> stage_2_e4_cols, const unsigned memory_args_start,
                                                     const unsigned log_n) {
  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  // Zeroing the last row for stage 2 bf and e4 args is handled by lookup_args_kernel.
  if (gid >= n - 1)
    return;

  stage_2_e4_cols.add_row(gid);
  stage_2_e4_cols.add_col(memory_args_start);
  memory_cols.add_row(gid);

  // Compute write_timestamp_contribution, common across accesses
  const bf write_timestamp_low = memory_cols.get_at_col(register_and_indirect_accesses.write_timestamp_col);
  const e4 write_timestamp_low_contribution = e4::mul(write_timestamp_low, challenges.timestamp_low_challenge);
  const bf write_timestamp_high = memory_cols.get_at_col(register_and_indirect_accesses.write_timestamp_col + 1);
  const e4 write_timestamp_high_contribution = e4::mul(write_timestamp_high, challenges.timestamp_high_challenge);
  const e4 write_timestamp_contribution = e4::add(write_timestamp_low_contribution, write_timestamp_high_contribution);

  e4 num_over_denom_acc{};
  unsigned flat_indirect_idx = 0;

#pragma unroll 1
  for (unsigned i = 0; i < register_and_indirect_accesses.num_register_accesses; i++) {
    unsigned base_low;
    unsigned base_high;
    // Register contribution
    {
      const auto &register_access = register_and_indirect_accesses.register_accesses[i];

      // TODO: this initial constant contribution could be precomputed and stashed
      e4 numerator = register_access.gamma_plus_one_plus_address_low_contribution;

      e4 denom{};

      if (register_access.is_write) {
        denom = numerator;

        const bf read_value_low = memory_cols.get_at_col(register_access.read_value_col);
        denom = e4::add(denom, e4::mul(challenges.value_low_challenge, read_value_low));
        base_low = bf::into_canonical(read_value_low).limb;
        const bf read_value_high = memory_cols.get_at_col(register_access.read_value_col + 1);
        denom = e4::add(denom, e4::mul(challenges.value_high_challenge, read_value_high));
        base_high = bf::into_canonical(read_value_high).limb;

        const bf write_value_low = memory_cols.get_at_col(register_access.maybe_write_value_col);
        numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, write_value_low));
        const bf write_value_high = memory_cols.get_at_col(register_access.maybe_write_value_col + 1);
        numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, write_value_high));
      } else {
        const bf value_low = memory_cols.get_at_col(register_access.read_value_col);
        numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, value_low));
        base_low = bf::into_canonical(value_low).limb;
        const bf value_high = memory_cols.get_at_col(register_access.read_value_col + 1);
        numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, value_high));
        base_high = bf::into_canonical(value_high).limb;

        denom = numerator;
      }

      numerator = e4::add(numerator, write_timestamp_contribution);

      const bf read_timestamp_low = memory_cols.get_at_col(register_access.read_timestamp_col);
      denom = e4::add(denom, e4::mul(challenges.timestamp_low_challenge, read_timestamp_low));
      const bf read_timestamp_high = memory_cols.get_at_col(register_access.read_timestamp_col + 1);
      denom = e4::add(denom, e4::mul(challenges.timestamp_high_challenge, read_timestamp_high));

      if (i == 0)
        num_over_denom_acc = numerator;
      else
        num_over_denom_acc = e4::mul(num_over_denom_acc, numerator);
      e4 denom_inv{e4::inv(denom)};
      num_over_denom_acc = e4::mul(num_over_denom_acc, denom_inv);
      stage_2_e4_cols.set(num_over_denom_acc);
      stage_2_e4_cols.add_col(1);
    }

    const unsigned lim = flat_indirect_idx + register_and_indirect_accesses.indirect_accesses_per_register_access[i];
#pragma unroll 1
    for (; flat_indirect_idx < lim; flat_indirect_idx++) {
      const auto &indirect_access = register_and_indirect_accesses.indirect_accesses[flat_indirect_idx];

      const unsigned address = base_low + indirect_access.offset;
      const unsigned of = address >> 16;
      const bf address_low = bf{address & 0x0000ffff};
      const bf address_high = bf{base_high + of};

      e4 numerator{challenges.gamma};
      numerator = e4::add(numerator, e4::mul(challenges.address_low_challenge, address_low));
      numerator = e4::add(numerator, e4::mul(challenges.address_high_challenge, address_high));

      e4 denom{};

      if (indirect_access.is_write) {
        denom = numerator;

        const bf read_value_low = memory_cols.get_at_col(indirect_access.read_value_col);
        denom = e4::add(denom, e4::mul(challenges.value_low_challenge, read_value_low));
        const bf read_value_high = memory_cols.get_at_col(indirect_access.read_value_col + 1);
        denom = e4::add(denom, e4::mul(challenges.value_high_challenge, read_value_high));

        const bf write_value_low = memory_cols.get_at_col(indirect_access.maybe_write_value_col);
        numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, write_value_low));
        const bf write_value_high = memory_cols.get_at_col(indirect_access.maybe_write_value_col + 1);
        numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, write_value_high));
      } else {
        const bf value_low = memory_cols.get_at_col(indirect_access.read_value_col);
        numerator = e4::add(numerator, e4::mul(challenges.value_low_challenge, value_low));
        const bf value_high = memory_cols.get_at_col(indirect_access.read_value_col + 1);
        numerator = e4::add(numerator, e4::mul(challenges.value_high_challenge, value_high));

        denom = numerator;
      }

      numerator = e4::add(numerator, write_timestamp_contribution);

      const bf read_timestamp_low = memory_cols.get_at_col(indirect_access.read_timestamp_col);
      denom = e4::add(denom, e4::mul(challenges.timestamp_low_challenge, read_timestamp_low));
      const bf read_timestamp_high = memory_cols.get_at_col(indirect_access.read_timestamp_col + 1);
      denom = e4::add(denom, e4::mul(challenges.timestamp_high_challenge, read_timestamp_high));

      // flush result
      num_over_denom_acc = e4::mul(num_over_denom_acc, numerator);
      e4 denom_inv{e4::inv(denom)};
      num_over_denom_acc = e4::mul(num_over_denom_acc, denom_inv);
      stage_2_e4_cols.set(num_over_denom_acc);
      stage_2_e4_cols.add_col(1);
    }
  }
}

} // namespace airbender::stage2