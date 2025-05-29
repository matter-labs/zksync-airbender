#include "arg_utils.cuh"
#include "context.cuh"
#include "ops_complex.cuh"
#include "vectorized.cuh"

using namespace field;
using namespace memory;

using bf = base_field;
using e2 = ext2_field;
using e4 = ext4_field;

/// These values are hand-picked, so that the biggest circuit (bigint) fits.
/// What is here must match values from stage_3_kernels.rs
constexpr unsigned MAX_NON_BOOLEAN_CONSTRAINTS = 192;
constexpr unsigned MAX_TERMS = 1824;
constexpr unsigned MAX_EXPLICIT_COEFFS = 632;
constexpr unsigned MAX_FLAT_COL_IDXS = 3488;
constexpr uint8_t COEFF_IS_ONE = 0x00;
constexpr uint8_t COEFF_IS_MINUS_ONE = 0x01;
// constexpr uint8_t COEFF_IS_EXPLICIT = 0x02; // technically unused, "default" case

extern "C" struct FlattenedGenericConstraintsMetadata {
  const uint8_t coeffs_info[MAX_TERMS];
  const bf explicit_coeffs[MAX_EXPLICIT_COEFFS];
  const uint16_t col_idxs[MAX_FLAT_COL_IDXS];
  // I could bit-pack these but it's more trouble than it's worth
  const uchar2 num_linear_and_quadratic_terms_per_constraint[MAX_NON_BOOLEAN_CONSTRAINTS];
  // TODO: consider making this array for quadratic constraints only.
  // In practice there are relatively few linear constraints so it doesn't make much difference.
  const e2 decompression_factor;
  const e2 decompression_factor_squared;
  const e2 every_row_zerofier;
  const e2 omega_inv;
  const unsigned current_flat_col_idx;
  const unsigned current_flat_term_idx;
  const unsigned num_boolean_constraints;
  const unsigned num_non_boolean_quadratic_constraints;
  const unsigned num_non_boolean_constraints;
};

template <typename T>
DEVICE_FORCEINLINE void maybe_apply_coeff(const T &metadata, const unsigned coeff_idx, unsigned &explicit_coeff_idx, field::base_field &val) {
  switch (metadata.coeffs_info[coeff_idx]) {
  case COEFF_IS_ONE:
    break;
  case COEFF_IS_MINUS_ONE:
    val = field::base_field::neg(val);
    break;
  default:
    val = field::base_field::mul(val, metadata.explicit_coeffs[explicit_coeff_idx++]);
  }
}

EXTERN __launch_bounds__(128, 8) __global__
    void generic_constraints_kernel(__grid_constant__ const FlattenedGenericConstraintsMetadata metadata, matrix_getter<bf, ld_modifier::cg> witness_cols,
                                    matrix_getter<bf, ld_modifier::cg> memory_cols, vector_getter<e4, ld_modifier::ca> alphas,
                                    vectorized_e4_matrix_setter<st_modifier::cs> quotient, const unsigned log_n) {
  const unsigned n = 1 << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= n)
    return;

  witness_cols.add_row(gid);
  memory_cols.add_row(gid);
  quotient.add_row(gid);

  e4 acc_linear{e4::zero()};
  e4 acc_quadratic{e4::zero()};

  // Boolean constraints
  for (unsigned constraint = 0; constraint < metadata.num_boolean_constraints; constraint++) {
    // generic boolean constraints should act on witness cols only (we assert this on the Rust side)
    const bf val_neg = bf::neg(witness_cols.get_at_col(metadata.col_idxs[constraint]));
    const bf val_squared = bf::mul(val_neg, val_neg);
    const e4 alpha_power = (alphas++).get();
    acc_quadratic = e4::add(acc_quadratic, e4::mul(alpha_power, val_squared));
    acc_linear = e4::add(acc_linear, e4::mul(alpha_power, val_neg));
  }

  unsigned flat_term_idx = 0;
  unsigned flat_col_idx = metadata.num_boolean_constraints;
  unsigned explicit_coeff_idx = 0;

  // Non-boolean quadratic constraints
  // Each contains at least one quadratic term and zero or more linear terms.
  for (unsigned constraint = 0; constraint < metadata.num_non_boolean_quadratic_constraints; constraint++) {
    const uchar2 num_linear_and_quadratic_terms = metadata.num_linear_and_quadratic_terms_per_constraint[constraint];
    const unsigned num_quadratic_terms = num_linear_and_quadratic_terms.x;
    const unsigned num_linear_terms = num_linear_and_quadratic_terms.y;

    bf quadratic_contribution{bf::zero()};
    unsigned lim = flat_term_idx + num_quadratic_terms;
    for (; flat_term_idx < lim; flat_term_idx++) {
      // Strangely, selecting between witness or memory cols incurs a 10-15% performance hit for this kernel
      // for n=2^22, but not for 2^21.
      // TODO: Double check performance for eventual production sizes.
      const bf val0 = get_witness_or_memory(metadata.col_idxs[flat_col_idx++], witness_cols, memory_cols);
      const bf val1 = get_witness_or_memory(metadata.col_idxs[flat_col_idx++], witness_cols, memory_cols);
      bf val = bf::mul(val0, val1);
      maybe_apply_coeff(metadata, flat_term_idx, explicit_coeff_idx, val);
      quadratic_contribution = bf::add(quadratic_contribution, val);
    }
    const e4 alpha_power = (alphas++).get();
    acc_quadratic = e4::add(acc_quadratic, e4::mul(alpha_power, quadratic_contribution));

    if (num_linear_terms > 0) {
      bf linear_contribution{bf::zero()};
      lim = flat_term_idx + num_linear_terms;
      for (; flat_term_idx < lim; flat_term_idx++) {
        bf val = get_witness_or_memory(metadata.col_idxs[flat_col_idx++], witness_cols, memory_cols);
        maybe_apply_coeff(metadata, flat_term_idx, explicit_coeff_idx, val);
        linear_contribution = bf::add(linear_contribution, val);
      }
      acc_linear = e4::add(acc_linear, e4::mul(alpha_power, linear_contribution));
    }
  }

  // Linear constraints
  for (unsigned constraint = metadata.num_non_boolean_quadratic_constraints; constraint < metadata.num_non_boolean_constraints; constraint++) {
    const uchar2 num_linear_and_quadratic_terms = metadata.num_linear_and_quadratic_terms_per_constraint[constraint];
    const unsigned num_linear_terms = num_linear_and_quadratic_terms.y;

    bf linear_contribution{bf::zero()};
    const unsigned lim = flat_term_idx + num_linear_terms;
    for (; flat_term_idx < lim; flat_term_idx++) {
      bf val = get_witness_or_memory(metadata.col_idxs[flat_col_idx++], witness_cols, memory_cols);
      maybe_apply_coeff(metadata, flat_term_idx, explicit_coeff_idx, val);
      linear_contribution = bf::add(linear_contribution, val);
    }

    const e4 alpha_power = (alphas++).get();
    acc_linear = e4::add(acc_linear, e4::mul(alpha_power, linear_contribution));
  }

  acc_quadratic = e4::mul(acc_quadratic, metadata.decompression_factor_squared);
  acc_linear = e4::mul(acc_linear, metadata.decompression_factor);
  e4 acc = e4::add(acc_quadratic, acc_linear);
  quotient.set(acc);
}

constexpr unsigned LOOKUP_VAL_IS_COL_FLAG = 255;

constexpr unsigned DELEGATED_MAX_WIDTH_3_LOOKUPS = 224;
constexpr unsigned DELEGATED_MAX_WIDTH_3_LOOKUP_VALS = 640;
constexpr unsigned DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS = 1408;
constexpr unsigned DELEGATED_MAX_WIDTH_3_LOOKUP_COLS = 1888;

extern "C" struct DelegatedWidth3LookupsLayout {
  const unsigned coeffs[DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS];
  const uint16_t col_idxs[DELEGATED_MAX_WIDTH_3_LOOKUP_COLS];
  const uint8_t num_terms_per_expression[DELEGATED_MAX_WIDTH_3_LOOKUP_VALS];
  const bool table_id_is_col[DELEGATED_MAX_WIDTH_3_LOOKUPS];
  const uint16_t e4_arg_cols[DELEGATED_MAX_WIDTH_3_LOOKUPS];
  const unsigned helpers_offset;
  const unsigned num_helpers_used;
  const unsigned num_lookups;
  const unsigned e4_arg_cols_start;
};

constexpr unsigned NON_DELEGATED_MAX_WIDTH_3_LOOKUPS = 24;
constexpr unsigned NON_DELEGATED_MAX_WIDTH_3_LOOKUP_VALS = 72;
constexpr unsigned NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS = 32;
constexpr unsigned NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COLS = 96;

extern "C" struct NonDelegatedWidth3LookupsLayout {
  const unsigned coeffs[NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COEFFS];
  const uint16_t col_idxs[NON_DELEGATED_MAX_WIDTH_3_LOOKUP_COLS];
  const uint8_t num_terms_per_expression[NON_DELEGATED_MAX_WIDTH_3_LOOKUP_VALS];
  const bool table_id_is_col[NON_DELEGATED_MAX_WIDTH_3_LOOKUPS];
  const uint16_t e4_arg_cols[NON_DELEGATED_MAX_WIDTH_3_LOOKUPS];
  const unsigned helpers_offset;
  const unsigned num_helpers_used;
  const unsigned num_lookups;
  const unsigned e4_arg_cols_start;
};

template <typename T>
DEVICE_FORCEINLINE void enforce_width_3_lookup_args_construction(const T &layout, const matrix_getter<bf, ld_modifier::cg> &witness_cols,
                                                                 const matrix_getter<bf, ld_modifier::cg> &memory_cols,
                                                                 const vectorized_e4_matrix_getter<ld_modifier::cg> &stage_2_e4_cols,
                                                                 vector_getter<e4, ld_modifier::ca> &helpers, e4 &acc_quadratic) {
  unsigned col_idx = 0;
  unsigned val_idx = 0;
  unsigned coeff_idx = 0;
  for (unsigned term_idx = 0; term_idx < layout.num_lookups; term_idx++) {
    e4 acc = (helpers++).get();
    if (layout.table_id_is_col[term_idx]) {
      // Should be witness cols (we assert this on the Rust side)
      const bf id = witness_cols.get_at_col(layout.col_idxs[col_idx++]);
      acc = e4::add(acc, e4::mul((helpers++).get(), id));
    }
#pragma unroll
    for (unsigned j = 0; j < NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1; j++) {
      const unsigned num_expr_terms = layout.num_terms_per_expression[val_idx++];
      if (num_expr_terms == LOOKUP_VAL_IS_COL_FLAG) {
        const bf val = get_witness_or_memory(layout.col_idxs[col_idx++], witness_cols, memory_cols);
        acc = e4::add(acc, e4::mul((helpers++).get(), val));
      } else {
        bf val{bf::zero()};
        const unsigned lim = col_idx + num_expr_terms;
        for (; col_idx < lim; col_idx++) {
          bf next = get_witness_or_memory(layout.col_idxs[col_idx], witness_cols, memory_cols);
          apply_coeff(layout.coeffs[coeff_idx++], next);
          val = bf::add(val, next);
        }
        if (num_expr_terms > 0) {
          acc = e4::add(acc, e4::mul((helpers++).get(), val));
        }
      }
    }
    const e4 e4_arg = stage_2_e4_cols.get_at_col(layout.e4_arg_cols[term_idx]);
    acc = e4::mul(acc, e4_arg);
    acc_quadratic = e4::add(acc_quadratic, acc);
  }
}

EXTERN __launch_bounds__(128, 8) __global__
    void delegated_width_3_lookups_kernel(__grid_constant__ const DelegatedWidth3LookupsLayout layout, matrix_getter<bf, ld_modifier::cg> witness_cols,
                                          matrix_getter<bf, ld_modifier::cg> memory_cols, vectorized_e4_matrix_getter<ld_modifier::cg> stage_2_e4_cols,
                                          vector_getter<e4, ld_modifier::ca> helpers,
                                          vectorized_e4_matrix_getter_setter<ld_modifier::cs, st_modifier::cs> quotient, const e2 decompression_factor_squared,
                                          const unsigned log_n) {
  const unsigned n = 1 << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= n)
    return;

  witness_cols.add_row(gid);
  memory_cols.add_row(gid);
  stage_2_e4_cols.add_row(gid);
  quotient.add_row(gid);
  helpers += layout.helpers_offset;

  e4 acc_quadratic{e4::zero()};

  enforce_width_3_lookup_args_construction(layout, witness_cols, memory_cols, stage_2_e4_cols, helpers, acc_quadratic);

  acc_quadratic = e4::mul(acc_quadratic, decompression_factor_squared);
  const e4 current_quotient = quotient.get();
  acc_quadratic = e4::add(acc_quadratic, current_quotient);
  quotient.set(acc_quadratic);
}

// Assumes pred is a boolean (0 or 1) and enforces (pred - 1) * val == 0.
DEVICE_FORCEINLINE void enforce_val_zero_if_pred_zero(const bf predicate, const bf val, vector_getter<e4, ld_modifier::ca> &alphas, e4 &acc_quadratic,
                                                      e4 &acc_linear) {
  const e4 alpha_power = (alphas++).get();
  const bf prod = bf::mul(predicate, val);
  acc_quadratic = e4::add(acc_quadratic, e4::mul(alpha_power, prod));
  acc_linear = e4::add(acc_linear, e4::mul(alpha_power, bf::neg(val)));
}

DEVICE_FORCEINLINE void enforce_width_1_bf_arg_construction(const bf a, const bf b, const bf bf_arg, vector_getter<e4, ld_modifier::ca> &alphas,
                                                            vector_getter<e4, ld_modifier::ca> &helpers, e4 &acc_linear, e4 &acc_quadratic) {
  const e4 alpha = (alphas++).get();
  const bf prod = bf::mul(a, b);
  acc_quadratic = e4::add(acc_quadratic, e4::mul(alpha, prod));
  acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::neg(bf_arg)));
}

DEVICE_FORCEINLINE void enforce_width_1_e4_arg_construction(const bf a, const bf b, const bf bf_arg, const unsigned e4_arg_idx,
                                                            const vectorized_e4_matrix_getter<ld_modifier::cg> &stage_2_e4_cols,
                                                            vector_getter<e4, ld_modifier::ca> &alphas, vector_getter<e4, ld_modifier::ca> &helpers,
                                                            e4 &acc_linear, e4 &acc_quadratic) {
  const e4 alpha = (alphas++).get();
  const bf sum = bf::add(a, b);
  // Thanks to precomputed helper factors, we get away with just one e4 x e4 mul.
  acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::neg(sum)));
  const e4 alpha_times_gamma = (helpers++).get();
  const e4 alpha_times_gamma_squared_adjusted = (helpers++).get();
  const e4 bf_arg_term = e4::mul(alpha, bf_arg);
  const e4 gamma_terms = e4::add(alpha_times_gamma_squared_adjusted, e4::mul(alpha_times_gamma, sum));
  const e4 denoms_prod = e4::add(bf_arg_term, gamma_terms);
  const e4 e4_arg = stage_2_e4_cols.get_at_col(e4_arg_idx);
  const e4 quadratic_term = e4::mul(e4_arg, denoms_prod);
  acc_quadratic = e4::add(acc_quadratic, quadratic_term);
}

template <typename T>
DEVICE_FORCEINLINE void enforce_range_check_expressions_with_constant_terms(const T &expressions, unsigned &i, unsigned &expression_idx,
                                                                            unsigned &flat_term_idx, const matrix_getter<bf, ld_modifier::cg> &witness_cols,
                                                                            const matrix_getter<bf, ld_modifier::cg> &memory_cols,
                                                                            const matrix_getter<bf, ld_modifier::cg> &stage_2_bf_cols,
                                                                            const vectorized_e4_matrix_getter<ld_modifier::cg> &stage_2_e4_cols,
                                                                            const unsigned expression_pair_bound, vector_getter<e4, ld_modifier::ca> &alphas,
                                                                            vector_getter<e4, ld_modifier::ca> &helpers, e4 &acc_linear, e4 &acc_quadratic) {
#pragma unroll
  for (; i < expression_pair_bound; i++) {
    bf a_and_b[2];
    eval_a_and_b<false>(a_and_b, expressions, expression_idx, flat_term_idx, witness_cols, memory_cols, false);
    const bf a = a_and_b[0]; // not including constant contribution
    const bf b = a_and_b[1]; // not including constant contribution
    const bf bf_arg = stage_2_bf_cols.get_at_col(expressions.bf_dst_cols[i]);
    const e4 alpha = (alphas++).get();
    const bf prod = bf::mul(a, b);
    acc_quadratic = e4::add(acc_quadratic, e4::mul(alpha, prod));
    const bf a_constant_term = expressions.constant_terms[expression_idx - 2];
    const bf b_constant_term = expressions.constant_terms[expression_idx - 1];
    const bf linear_contribution_from_a_b_constants = bf::add(bf::mul(a, b_constant_term), bf::mul(b, a_constant_term));
    acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::sub(linear_contribution_from_a_b_constants, bf_arg)));
    enforce_width_1_e4_arg_construction(a, b, bf_arg, expressions.e4_dst_cols[i], stage_2_e4_cols, alphas, helpers, acc_linear, acc_quadratic);
  }
}

extern "C" struct MultiplicitiesLayout {
  const unsigned src_cols_start;
  const unsigned dst_cols_start;
  const unsigned setup_cols_start;
  const unsigned num_dst_cols;
};

template <unsigned ENTRY_WIDTH>
DEVICE_FORCEINLINE void
enforce_lookup_multiplicities(const MultiplicitiesLayout &layout, const matrix_getter<bf, ld_modifier::cg> &setup_cols,
                              const matrix_getter<bf, ld_modifier::cg> &witness_cols, const vectorized_e4_matrix_getter<ld_modifier::cg> &stage_2_e4_cols,
                              vector_getter<e4, ld_modifier::ca> &alphas, vector_getter<e4, ld_modifier::ca> &helpers, e4 &acc_linear, e4 &acc_quadratic) {
  for (unsigned i = 0; i < layout.num_dst_cols; i++) {
    const e4 alpha = (alphas++).get();
    const bf m = witness_cols.get_at_col(layout.src_cols_start + i);
    acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::neg(m)));
    e4 denom = (helpers++).get();
    const unsigned setup_cols_start = layout.setup_cols_start + i * ENTRY_WIDTH;
    denom = e4::add(denom, e4::mul(alpha, setup_cols.get_at_col(setup_cols_start)));
    if (ENTRY_WIDTH > 1) { // hint to compiler to optimize this out if possible
#pragma unroll
      for (unsigned i = 1; i < ENTRY_WIDTH; i++) {
        const e4 adjusted_linearization_challenge = (helpers++).get();
        const bf val = setup_cols.get_at_col(setup_cols_start + i);
        denom = e4::add(denom, e4::mul(adjusted_linearization_challenge, val));
      }
    }
    const e4 e4_arg = stage_2_e4_cols.get_at_col(layout.dst_cols_start + i);
    denom = e4::mul(denom, e4_arg);
    acc_quadratic = e4::add(acc_quadratic, denom);
  }
}

constexpr unsigned MAX_STATE_LINKAGE_CONSTRAINTS = 2;

extern "C" struct StateLinkageConstraints {
  const unsigned srcs[MAX_STATE_LINKAGE_CONSTRAINTS];
  const unsigned dsts[MAX_STATE_LINKAGE_CONSTRAINTS];
  const unsigned num_constraints;
};

constexpr bf SHIFT_16 = bf{1 << 16};

constexpr unsigned MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW = 8;
constexpr unsigned MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW = 8;

extern "C" struct BoundaryConstraints {
  const unsigned first_row_cols[MAX_BOUNDARY_CONSTRAINTS_FIRST_ROW];
  const unsigned one_before_last_row_cols[MAX_BOUNDARY_CONSTRAINTS_ONE_BEFORE_LAST_ROW];
  const unsigned num_first_row;
  const unsigned num_one_before_last_row;
};

extern "C" struct ConstantsTimesChallenges {
  const e4 first_row;
  const e4 one_before_last_row;
  const e4 sum;
};

// TODO once constraints are done
//  - think about the most sensible way to split them up into multiple kernels.
//    e.g. one kernel for memory-col-heavy terms and one kernel for witness-col-heavy terms.
//  - Turn e4::sub contributions to acc_linear into e4::adds and negate acc_linear once at the end
EXTERN __launch_bounds__(128, 8) __global__ void hardcoded_constraints_kernel(
    matrix_getter<bf, ld_modifier::cg> setup_cols, matrix_getter<bf, ld_modifier::cg> witness_cols, matrix_getter<bf, ld_modifier::cg> memory_cols,
    matrix_getter<bf, ld_modifier::cg> stage_2_bf_cols, vectorized_e4_matrix_getter<ld_modifier::cg> stage_2_e4_cols, const bool process_delegations,
    const bool handle_delegation_requests, const unsigned delegation_aux_poly_col, __grid_constant__ const DelegationChallenges delegation_challenges,
    __grid_constant__ const DelegationProcessingMetadata delegation_processing_metadata,
    __grid_constant__ const DelegationRequestMetadata delegation_request_metadata, const unsigned memory_args_start, const unsigned memory_grand_product_col,
    __grid_constant__ const LazyInitTeardownLayout lazy_init_teardown_layout, __grid_constant__ const ShuffleRamAccesses shuffle_ram_accesses,
    const bool process_batch_ram_access, __grid_constant__ const BatchedRamAccesses batched_ram_accesses, const bool process_registers_and_indirect_access,
    __grid_constant__ const RegisterAndIndirectAccesses register_and_indirect_accesses, __grid_constant__ const RangeCheckArgsLayout range_check_16_layout,
    __grid_constant__ const FlattenedLookupExpressionsLayout expressions,
    __grid_constant__ const FlattenedLookupExpressionsForShuffleRamLayout expressions_for_shuffle_ram,
    __grid_constant__ const NonDelegatedWidth3LookupsLayout width_3_lookups_layout,
    __grid_constant__ const MultiplicitiesLayout range_check_16_multiplicities_layout,
    __grid_constant__ const MultiplicitiesLayout timestamp_range_check_multiplicities_layout,
    __grid_constant__ const MultiplicitiesLayout generic_lookup_multiplicities_layout,
    __grid_constant__ const StateLinkageConstraints state_linkage_constraints, __grid_constant__ const BoundaryConstraints boundary_constraints,
    vector_getter<e4, ld_modifier::ca> alphas, vector_getter<e4, ld_modifier::ca> alphas_every_row_except_last_two, vector_getter<e4, ld_modifier::ca> betas,
    vector_getter<e4, ld_modifier::ca> helpers, const ConstantsTimesChallenges *constants_times_challenges,
    vectorized_e4_matrix_getter_setter<ld_modifier::cs, st_modifier::cs> quotient, const bf memory_timestamp_high_from_circuit_idx,
    const e2 decompression_factor, const e2 decompression_factor_squared, const e2 every_row_zerofier, const e2 omega_inv, const e2 omega_inv_squared,
    const unsigned log_n) {
  const unsigned n = 1 << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= n)
    return;

  setup_cols.add_row(gid);
  witness_cols.add_row(gid);
  memory_cols.add_row(gid);
  stage_2_bf_cols.add_row(gid);
  stage_2_e4_cols.add_row(gid);
  quotient.add_row(gid);

  e4 acc_linear{e4::zero()};
  e4 acc_quadratic{e4::zero()};

  // TODO: consider factoring out the predicate from some of the sequences below, accumulating to a temporary acc_quadratic,
  // and multiplying the temporary acc_quadratic by predicate at the end of each sequence.
  if (process_delegations) {
    const auto &metadata = delegation_processing_metadata;
    const bf predicate = memory_cols.get_at_col(metadata.multiplicity_col);
    const bf vals[4] = {predicate, memory_cols.get_at_col(metadata.abi_mem_offset_high_col), memory_cols.get_at_col(metadata.write_timestamp_col),
                        memory_cols.get_at_col(metadata.write_timestamp_col + 1)};
    // the first iteration enforces that predicate is a boolean. conveniently, this can use the same function.
#pragma unroll
    for (unsigned i = 0; i < 4; i++)
      enforce_val_zero_if_pred_zero(predicate, vals[i], alphas, acc_quadratic, acc_linear);

    if (process_batch_ram_access) {
#pragma unroll
      for (unsigned i = 0; i < batched_ram_accesses.num_accesses; i++) {
        const auto &access = batched_ram_accesses.accesses[i];
        enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_timestamp_col), alphas, acc_quadratic, acc_linear);
        enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_timestamp_col + 1), alphas, acc_quadratic, acc_linear);
        enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_value_col), alphas, acc_quadratic, acc_linear);
        enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_value_col + 1), alphas, acc_quadratic, acc_linear);
        if (access.is_write) {
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.maybe_write_value_col), alphas, acc_quadratic, acc_linear);
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.maybe_write_value_col + 1), alphas, acc_quadratic, acc_linear);
        }
      }
    }

    if (process_registers_and_indirect_access) {
      unsigned flat_indirect_idx = 0;
#pragma unroll
      for (unsigned i = 0; i < register_and_indirect_accesses.num_register_accesses; i++) {
        {
          const auto &access = register_and_indirect_accesses.register_accesses[i];
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_timestamp_col), alphas, acc_quadratic, acc_linear);
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_timestamp_col + 1), alphas, acc_quadratic, acc_linear);
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_value_col), alphas, acc_quadratic, acc_linear);
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_value_col + 1), alphas, acc_quadratic, acc_linear);
          if (access.is_write) {
            enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.maybe_write_value_col), alphas, acc_quadratic, acc_linear);
            enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.maybe_write_value_col + 1), alphas, acc_quadratic, acc_linear);
          }
        }
        const unsigned num_indirect_accesses = register_and_indirect_accesses.indirect_accesses_per_register_access[i];
#pragma unroll 1
        for (unsigned j = 0; j < num_indirect_accesses; j++, flat_indirect_idx++) {
          const auto &access = register_and_indirect_accesses.indirect_accesses[flat_indirect_idx];
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_timestamp_col), alphas, acc_quadratic, acc_linear);
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_timestamp_col + 1), alphas, acc_quadratic, acc_linear);
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_value_col), alphas, acc_quadratic, acc_linear);
          enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.read_value_col + 1), alphas, acc_quadratic, acc_linear);
          if (access.is_write) {
            enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.maybe_write_value_col), alphas, acc_quadratic, acc_linear);
            enforce_val_zero_if_pred_zero(predicate, memory_cols.get_at_col(access.maybe_write_value_col + 1), alphas, acc_quadratic, acc_linear);
          }
          if (j > 0 && access.address_derivation_carry_bit_num_elements > 0) {
            // Boolean check for carry bit
            const bf carry_bit = memory_cols.get_at_col(access.address_derivation_carry_bit_col);
            enforce_val_zero_if_pred_zero(carry_bit, carry_bit, alphas, acc_quadratic, acc_linear);
          }
        }
      }
    }
  }

  // Range check 16 and timestamp range check args
  {
#pragma unroll
    for (unsigned i = 0; i < range_check_16_layout.num_dst_cols; i++) {
      const unsigned src = 2 * i + range_check_16_layout.src_cols_start;
      const bf a = witness_cols.get_at_col(src);
      const bf b = witness_cols.get_at_col(src + 1);
      const bf bf_arg = stage_2_bf_cols.get_at_col(range_check_16_layout.bf_args_start + i);
      enforce_width_1_bf_arg_construction(a, b, bf_arg, alphas, helpers, acc_linear, acc_quadratic);
      enforce_width_1_e4_arg_construction(a, b, bf_arg, range_check_16_layout.e4_args_start + i, stage_2_e4_cols, alphas, helpers, acc_linear, acc_quadratic);
    }

    unsigned i{0}, expression_idx{0}, flat_term_idx{0};

    if (expressions.range_check_16_constant_terms_are_zero) {
#pragma unroll
      for (; i < expressions.num_range_check_16_expression_pairs; i++) {
        bf a_and_b[2];
        eval_a_and_b<false>(a_and_b, expressions, expression_idx, flat_term_idx, witness_cols, memory_cols, true);
        const bf bf_arg = stage_2_bf_cols.get_at_col(expressions.bf_dst_cols[i]);
        enforce_width_1_bf_arg_construction(a_and_b[0], a_and_b[1], bf_arg, alphas, helpers, acc_linear, acc_quadratic);
        enforce_width_1_e4_arg_construction(a_and_b[0], a_and_b[1], bf_arg, expressions.e4_dst_cols[i], stage_2_e4_cols, alphas, helpers, acc_linear,
                                            acc_quadratic);
      }
    } else {
      enforce_range_check_expressions_with_constant_terms(expressions, i, expression_idx, flat_term_idx, witness_cols, memory_cols, stage_2_bf_cols,
                                                          stage_2_e4_cols, expressions.num_range_check_16_expression_pairs, alphas, helpers, acc_linear,
                                                          acc_quadratic);
    }

    if (lazy_init_teardown_layout.process_shuffle_ram_init) {
      const bf a = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start);
      const bf b = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start + 1);
      const bf bf_arg = stage_2_bf_cols.get_at_col(lazy_init_teardown_layout.bf_arg_col);
      enforce_width_1_bf_arg_construction(a, b, bf_arg, alphas, helpers, acc_linear, acc_quadratic);
      enforce_width_1_e4_arg_construction(a, b, bf_arg, lazy_init_teardown_layout.e4_arg_col, stage_2_e4_cols, alphas, helpers, acc_linear, acc_quadratic);
    }

    if (expressions.timestamp_constant_terms_are_zero) {
      const unsigned expression_pair_bound = i + expressions.num_timestamp_expression_pairs;
#pragma unroll
      for (; i < expression_pair_bound; i++) {
        bf a_and_b[2];
        eval_a_and_b<false>(a_and_b, expressions, expression_idx, flat_term_idx, witness_cols, memory_cols, true);
        const bf bf_arg = stage_2_bf_cols.get_at_col(expressions.bf_dst_cols[i]);
        enforce_width_1_bf_arg_construction(a_and_b[0], a_and_b[1], bf_arg, alphas, helpers, acc_linear, acc_quadratic);
        enforce_width_1_e4_arg_construction(a_and_b[0], a_and_b[1], bf_arg, expressions.e4_dst_cols[i], stage_2_e4_cols, alphas, helpers, acc_linear,
                                            acc_quadratic);
      }
    } else {
      const unsigned expression_pair_bound = i + expressions.num_timestamp_expression_pairs;
      enforce_range_check_expressions_with_constant_terms(expressions, i, expression_idx, flat_term_idx, witness_cols, memory_cols, stage_2_bf_cols,
                                                          stage_2_e4_cols, expression_pair_bound, alphas, helpers, acc_linear, acc_quadratic);
    }

    // TODO (optional): If i add a spurious "setup_cols" argument to the eval_a_and_b overload for non-shuffle-ram expressions,
    // I could use enforce_range_check_expressions_with_constant_terms here too.
#pragma unroll
    for (unsigned i = 0, expression_idx = 0, flat_term_idx = 0; i < expressions_for_shuffle_ram.num_expression_pairs; i++) {
      bf a_and_b[2];
      eval_a_and_b<false>(a_and_b, expressions_for_shuffle_ram, expression_idx, flat_term_idx, setup_cols, witness_cols, memory_cols);
      const bf a = a_and_b[0]; // not including constant contribution
      const bf b = a_and_b[1]; // not including constant contribution
      const bf bf_arg = stage_2_bf_cols.get_at_col(expressions_for_shuffle_ram.bf_dst_cols[i]);
      const e4 alpha = (alphas++).get();
      const bf prod = bf::mul(a, b);
      acc_quadratic = e4::add(acc_quadratic, e4::mul(alpha, prod));
      const bf a_constant_term = expressions_for_shuffle_ram.constant_terms[expression_idx - 2];
      const bf b_constant_term = expressions_for_shuffle_ram.constant_terms[expression_idx - 1];
      const bf b_constant_term_adjusted = bf::sub(b_constant_term, memory_timestamp_high_from_circuit_idx);
      const bf linear_contribution_from_a_b_constants = bf::add(bf::mul(a, b_constant_term_adjusted), bf::mul(b, a_constant_term));
      acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::sub(linear_contribution_from_a_b_constants, bf_arg)));
      enforce_width_1_e4_arg_construction(a, b, bf_arg, expressions_for_shuffle_ram.e4_dst_cols[i], stage_2_e4_cols, alphas, helpers, acc_linear,
                                          acc_quadratic);
    }
  }

  if (process_delegations) {
    // width 3 lookups were already handled by delegated_width_3_lookups_kernel.
    // width_3_lookups_layout is just a placeholder with enough info to account for the alphas and helpers the other kernel used.
    alphas += width_3_lookups_layout.num_lookups;
    helpers += width_3_lookups_layout.num_helpers_used;
  } else {
    enforce_width_3_lookup_args_construction(width_3_lookups_layout, witness_cols, memory_cols, stage_2_e4_cols, helpers, acc_quadratic);
    alphas += width_3_lookups_layout.num_lookups;
  }

  enforce_lookup_multiplicities<1>(range_check_16_multiplicities_layout, setup_cols, witness_cols, stage_2_e4_cols, alphas, helpers, acc_linear, acc_quadratic);
  enforce_lookup_multiplicities<1>(timestamp_range_check_multiplicities_layout, setup_cols, witness_cols, stage_2_e4_cols, alphas, helpers, acc_linear,
                                   acc_quadratic);
  enforce_lookup_multiplicities<NUM_LOOKUP_ARGUMENT_KEY_PARTS>(generic_lookup_multiplicities_layout, setup_cols, witness_cols, stage_2_e4_cols, alphas, helpers,
                                                               acc_linear, acc_quadratic);

  if (handle_delegation_requests) {
    const auto &metadata = delegation_request_metadata;
    const bf m = memory_cols.get_at_col(metadata.multiplicity_col);
    const e4 alpha = (alphas++).get();
    acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::neg(m)));
    e4 denom = (helpers++).get();
    denom = e4::add(denom, e4::mul(alpha, memory_cols.get_at_col(metadata.delegation_type_col)));
    denom = e4::add(denom, e4::mul((helpers++).get(), memory_cols.get_at_col(metadata.abi_mem_offset_high_col)));
    denom = e4::add(denom, e4::mul((helpers++).get(), setup_cols.get_at_col(metadata.timestamp_setup_col)));
    denom = e4::add(denom, e4::mul((helpers++).get(), setup_cols.get_at_col(metadata.timestamp_setup_col + 1)));
    const e4 e4_arg = stage_2_e4_cols.get_at_col(delegation_aux_poly_col);
    acc_quadratic = e4::add(acc_quadratic, e4::mul(e4_arg, denom));
  }

  if (process_delegations) {
    const auto &metadata = delegation_processing_metadata;
    const bf m = memory_cols.get_at_col(metadata.multiplicity_col);
    const e4 alpha = (alphas++).get();
    acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::neg(m)));
    e4 denom = (helpers++).get();
    denom = e4::add(denom, e4::mul((helpers++).get(), memory_cols.get_at_col(metadata.abi_mem_offset_high_col)));
    denom = e4::add(denom, e4::mul((helpers++).get(), memory_cols.get_at_col(metadata.write_timestamp_col)));
    denom = e4::add(denom, e4::mul((helpers++).get(), memory_cols.get_at_col(metadata.write_timestamp_col + 1)));
    const e4 e4_arg = stage_2_e4_cols.get_at_col(delegation_aux_poly_col);
    acc_quadratic = e4::add(acc_quadratic, e4::mul(e4_arg, denom));
  }

  if (lazy_init_teardown_layout.process_shuffle_ram_init) {

    e4 e4_arg_prev{};
    {
      const bf address_low = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start);
      const bf address_high = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start + 1);
      const bf value_low = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_value_start);
      const bf value_high = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_value_start + 1);
      const bf timestamp_low = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_timestamp_start);
      const bf timestamp_high = memory_cols.get_at_col(lazy_init_teardown_layout.teardown_timestamp_start + 1);
      const bf final_borrow = witness_cols.get_at_col(lazy_init_teardown_layout.init_address_final_borrow);

      // First, enforce lazy init address, value, and timestamp limbs are zero if "final borrow" is zero
      enforce_val_zero_if_pred_zero(final_borrow, address_low, alphas, acc_quadratic, acc_linear);
      enforce_val_zero_if_pred_zero(final_borrow, address_high, alphas, acc_quadratic, acc_linear);
      enforce_val_zero_if_pred_zero(final_borrow, value_low, alphas, acc_quadratic, acc_linear);
      enforce_val_zero_if_pred_zero(final_borrow, value_high, alphas, acc_quadratic, acc_linear);
      enforce_val_zero_if_pred_zero(final_borrow, timestamp_low, alphas, acc_quadratic, acc_linear);
      enforce_val_zero_if_pred_zero(final_borrow, timestamp_high, alphas, acc_quadratic, acc_linear);

      // now, enforce the lazy init arg itself
      e4 numerator = e4::mul((helpers++).get(), address_low);
      numerator = e4::add(numerator, e4::mul((helpers++).get(), address_high));
      acc_linear = e4::sub(acc_linear, numerator);

      e4 denom{numerator};
      denom = e4::add(denom, e4::mul((helpers++).get(), value_low));
      denom = e4::add(denom, e4::mul((helpers++).get(), value_high));
      denom = e4::add(denom, e4::mul((helpers++).get(), timestamp_low));
      denom = e4::add(denom, e4::mul((helpers++).get(), timestamp_high));

      const e4 alpha_times_gamma_adjusted = (helpers++).get();
      denom = e4::add(denom, alpha_times_gamma_adjusted);

      const e4 e4_arg = stage_2_e4_cols.get_at_col(memory_args_start);
      acc_quadratic = e4::add(acc_quadratic, e4::mul(e4_arg, denom));
      e4_arg_prev = e4_arg;

      alphas++; // advance alpha explicitly
    }

    // Some write timestamp limb contributions are common across accesses:
    const bf write_timestamp_in_setup_low = setup_cols.get_at_col(shuffle_ram_accesses.write_timestamp_in_setup_start);
    const bf write_timestamp_in_setup_high = setup_cols.get_at_col(shuffle_ram_accesses.write_timestamp_in_setup_start + 1);
#pragma unroll 1
    for (unsigned i = 0; i < shuffle_ram_accesses.num_accesses; i++) {
      const auto &access = shuffle_ram_accesses.accesses[i];

      const bf address_low = memory_cols.get_at_col(access.address_start);
      e4 numerator = e4::mul((helpers++).get(), address_low);

      if (access.is_register_only) {
        alphas++; // constant bf::one() is already accounted for in numerator constant helper
      } else {
        const bf address_high = memory_cols.get_at_col(access.address_start + 1);
        numerator = e4::add(numerator, e4::mul((helpers++).get(), address_high));
        numerator = e4::add(numerator, e4::mul((alphas++).get(), memory_cols.get_at_col(access.maybe_is_register_start)));
      }

      e4 denom{};

      const e4 value_low_helper = (helpers++).get();
      const e4 value_high_helper = (helpers++).get();
      if (access.is_write) {
        denom = numerator;

        const bf read_value_low = memory_cols.get_at_col(access.read_value_start);
        denom = e4::add(denom, e4::mul(value_low_helper, read_value_low));
        const bf read_value_high = memory_cols.get_at_col(access.read_value_start + 1);
        denom = e4::add(denom, e4::mul(value_high_helper, read_value_high));

        const bf write_value_low = memory_cols.get_at_col(access.maybe_write_value_start);
        numerator = e4::add(numerator, e4::mul(value_low_helper, write_value_low));
        const bf write_value_high = memory_cols.get_at_col(access.maybe_write_value_start + 1);
        numerator = e4::add(numerator, e4::mul(value_high_helper, write_value_high));
      } else {
        const bf value_low = memory_cols.get_at_col(access.read_value_start);
        numerator = e4::add(numerator, e4::mul(value_low_helper, value_low));
        const bf value_high = memory_cols.get_at_col(access.read_value_start + 1);
        numerator = e4::add(numerator, e4::mul(value_high_helper, value_high));

        denom = numerator;
      }

      const e4 timestamp_low_helper = (helpers++).get();
      const e4 timestamp_high_helper = (helpers++).get();

      const bf read_timestamp_low = memory_cols.get_at_col(access.read_timestamp_start);
      denom = e4::add(denom, e4::mul(timestamp_low_helper, read_timestamp_low));
      const bf read_timestamp_high = memory_cols.get_at_col(access.read_timestamp_start + 1);
      denom = e4::add(denom, e4::mul(timestamp_high_helper, read_timestamp_high));

      numerator = e4::add(numerator, e4::mul(timestamp_low_helper, write_timestamp_in_setup_low));
      numerator = e4::add(numerator, e4::mul(timestamp_high_helper, write_timestamp_in_setup_high));

      // adjusted constant contributions
      denom = e4::add(denom, (helpers++).get());
      numerator = e4::add(numerator, (helpers++).get());

      const e4 e4_arg = stage_2_e4_cols.get_at_col(memory_args_start + 1 + i);
      acc_quadratic = e4::add(acc_quadratic, e4::mul(e4_arg, denom));

      acc_quadratic = e4::sub(acc_quadratic, e4::mul(e4_arg_prev, numerator));
      e4_arg_prev = e4_arg;
    }
  }

  if (process_batch_ram_access) {
    // address_high and write_timestamp limbs are which is common across accesses
    const bf address_high = memory_cols.get_at_col(batched_ram_accesses.abi_mem_offset_high_col);
    const bf write_timestamp_low = memory_cols.get_at_col(batched_ram_accesses.write_timestamp_col);
    const bf write_timestamp_high = memory_cols.get_at_col(batched_ram_accesses.write_timestamp_col + 1);
#pragma unroll 1
    for (unsigned i = 0; i < batched_ram_accesses.num_accesses; i++) {
      const auto &access = batched_ram_accesses.accesses[i];

      e4 numerator = e4::mul((helpers++).get(), address_high);

      e4 denom{};

      const e4 value_low_helper = (helpers++).get();
      const e4 value_high_helper = (helpers++).get();
      if (access.is_write) {
        denom = numerator;

        const bf read_value_low = memory_cols.get_at_col(access.read_value_col);
        denom = e4::add(denom, e4::mul(value_low_helper, read_value_low));
        const bf read_value_high = memory_cols.get_at_col(access.read_value_col + 1);
        denom = e4::add(denom, e4::mul(value_high_helper, read_value_high));

        const bf write_value_low = memory_cols.get_at_col(access.maybe_write_value_col);
        numerator = e4::add(numerator, e4::mul(value_low_helper, write_value_low));
        const bf write_value_high = memory_cols.get_at_col(access.maybe_write_value_col + 1);
        numerator = e4::add(numerator, e4::mul(value_high_helper, write_value_high));
      } else {
        const bf value_low = memory_cols.get_at_col(access.read_value_col);
        numerator = e4::add(numerator, e4::mul(value_low_helper, value_low));
        const bf value_high = memory_cols.get_at_col(access.read_value_col + 1);
        numerator = e4::add(numerator, e4::mul(value_high_helper, value_high));

        denom = numerator;
      }

      const e4 timestamp_low_helper = (helpers++).get();
      const e4 timestamp_high_helper = (helpers++).get();

      numerator = e4::add(numerator, e4::mul(timestamp_low_helper, write_timestamp_low));
      numerator = e4::add(numerator, e4::mul(timestamp_high_helper, write_timestamp_high));

      const bf read_timestamp_low = memory_cols.get_at_col(access.read_timestamp_col);
      denom = e4::add(denom, e4::mul(timestamp_low_helper, read_timestamp_low));
      const bf read_timestamp_high = memory_cols.get_at_col(access.read_timestamp_col + 1);
      denom = e4::add(denom, e4::mul(timestamp_high_helper, read_timestamp_high));

      // adjusted constant contributions
      const e4 constant = (helpers++).get();
      denom = e4::add(denom, constant);
      const e4 e4_arg = stage_2_e4_cols.get_at_col(memory_args_start + i);
      acc_quadratic = e4::add(acc_quadratic, e4::mul(e4_arg, denom));

      // flush result
      if (i == 0) {
        acc_linear = e4::sub(acc_linear, numerator);
      } else {
        numerator = e4::add(numerator, constant);

        // TODO: When you have a batch ram test case again, move e4_arg_prev to registers,
        // as it is for the other two access types.
        const e4 e4_arg_prev = stage_2_e4_cols.get_at_col(memory_args_start + i - 1);
        acc_quadratic = e4::sub(acc_quadratic, e4::mul(e4_arg_prev, numerator));
      }
    }

    alphas += batched_ram_accesses.num_accesses;
  }

  if (process_registers_and_indirect_access) {
    const bf write_timestamp_low = memory_cols.get_at_col(register_and_indirect_accesses.write_timestamp_col);
    const bf write_timestamp_high = memory_cols.get_at_col(register_and_indirect_accesses.write_timestamp_col + 1);
    unsigned flat_indirect_idx = 0;
    e4 e4_arg_prev{};
#pragma unroll 1
    for (unsigned i = 0; i < register_and_indirect_accesses.num_register_accesses; i++) {
      bf base_low;
      bf base_high;
      {
        const auto &access = register_and_indirect_accesses.register_accesses[i];
        e4 numerator{};
        e4 denom{};

        const e4 value_low_helper = (helpers++).get();
        const e4 value_high_helper = (helpers++).get();
        if (access.is_write) {
          const bf read_value_low = memory_cols.get_at_col(access.read_value_col);
          denom = e4::mul(value_low_helper, read_value_low);
          const bf read_value_high = memory_cols.get_at_col(access.read_value_col + 1);
          denom = e4::add(denom, e4::mul(value_high_helper, read_value_high));

          // imitate arg construction
          base_low = bf::into_canonical(read_value_low);
          base_high = bf::into_canonical(read_value_high);

          const bf write_value_low = memory_cols.get_at_col(access.maybe_write_value_col);
          numerator = e4::mul(value_low_helper, write_value_low);
          const bf write_value_high = memory_cols.get_at_col(access.maybe_write_value_col + 1);
          numerator = e4::add(numerator, e4::mul(value_high_helper, write_value_high));
        } else {
          const bf value_low = memory_cols.get_at_col(access.read_value_col);
          numerator = e4::mul(value_low_helper, value_low);
          const bf value_high = memory_cols.get_at_col(access.read_value_col + 1);
          numerator = e4::add(numerator, e4::mul(value_high_helper, value_high));

          // imitate arg construction
          base_low = bf::into_canonical(value_low);
          base_high = bf::into_canonical(value_high);

          denom = numerator;
        }

        const e4 timestamp_low_helper = (helpers++).get();
        const e4 timestamp_high_helper = (helpers++).get();

        numerator = e4::add(numerator, e4::mul(timestamp_low_helper, write_timestamp_low));
        numerator = e4::add(numerator, e4::mul(timestamp_high_helper, write_timestamp_high));

        const bf read_timestamp_low = memory_cols.get_at_col(access.read_timestamp_col);
        denom = e4::add(denom, e4::mul(timestamp_low_helper, read_timestamp_low));
        const bf read_timestamp_high = memory_cols.get_at_col(access.read_timestamp_col + 1);
        denom = e4::add(denom, e4::mul(timestamp_high_helper, read_timestamp_high));

        // adjusted constant contributions
        const e4 constant = (helpers++).get();
        denom = e4::add(denom, constant);
        const e4 e4_arg = stage_2_e4_cols.get_at_col(memory_args_start + i + flat_indirect_idx);
        acc_quadratic = e4::add(acc_quadratic, e4::mul(e4_arg, denom));

        // flush result
        if (i == 0) {
          acc_linear = e4::sub(acc_linear, numerator);
          e4_arg_prev = e4_arg;
        } else {
          numerator = e4::add(numerator, constant);
          acc_quadratic = e4::sub(acc_quadratic, e4::mul(e4_arg_prev, numerator));
          e4_arg_prev = e4_arg;
        }
      }

      const unsigned start = flat_indirect_idx;
      const unsigned end = flat_indirect_idx + register_and_indirect_accesses.indirect_accesses_per_register_access[i];
#pragma unroll 1
      for (; flat_indirect_idx < end; flat_indirect_idx++) {
        const auto &access = register_and_indirect_accesses.indirect_accesses[flat_indirect_idx];
        e4 numerator{};
        e4 denom{};

        const e4 address_low_helper = (helpers++).get();
        const e4 address_high_helper = (helpers++).get();
        if (flat_indirect_idx == start || access.address_derivation_carry_bit_num_elements == 0) {
          numerator = e4::mul(address_low_helper, base_low);
          numerator = e4::add(numerator, e4::mul(address_high_helper, base_high));
        } else {
          const bf carry_bit = memory_cols.get_at_col(access.address_derivation_carry_bit_col);
          numerator = e4::mul(address_low_helper, bf::sub(base_low, bf::mul(carry_bit, SHIFT_16)));
          numerator = e4::add(numerator, e4::mul(address_high_helper, bf::add(base_high, carry_bit)));
        }

        const e4 value_low_helper = (helpers++).get();
        const e4 value_high_helper = (helpers++).get();
        if (access.is_write) {
          denom = numerator;

          const bf read_value_low = memory_cols.get_at_col(access.read_value_col);
          denom = e4::add(denom, e4::mul(value_low_helper, read_value_low));
          const bf read_value_high = memory_cols.get_at_col(access.read_value_col + 1);
          denom = e4::add(denom, e4::mul(value_high_helper, read_value_high));

          const bf write_value_low = memory_cols.get_at_col(access.maybe_write_value_col);
          numerator = e4::add(numerator, e4::mul(value_low_helper, write_value_low));
          const bf write_value_high = memory_cols.get_at_col(access.maybe_write_value_col + 1);
          numerator = e4::add(numerator, e4::mul(value_high_helper, write_value_high));
        } else {
          const bf value_low = memory_cols.get_at_col(access.read_value_col);
          numerator = e4::add(numerator, e4::mul(value_low_helper, value_low));
          const bf value_high = memory_cols.get_at_col(access.read_value_col + 1);
          numerator = e4::add(numerator, e4::mul(value_high_helper, value_high));

          denom = numerator;
        }

        const e4 timestamp_low_helper = (helpers++).get();
        const e4 timestamp_high_helper = (helpers++).get();

        numerator = e4::add(numerator, e4::mul(timestamp_low_helper, write_timestamp_low));
        numerator = e4::add(numerator, e4::mul(timestamp_high_helper, write_timestamp_high));

        const bf read_timestamp_low = memory_cols.get_at_col(access.read_timestamp_col);
        denom = e4::add(denom, e4::mul(timestamp_low_helper, read_timestamp_low));
        const bf read_timestamp_high = memory_cols.get_at_col(access.read_timestamp_col + 1);
        denom = e4::add(denom, e4::mul(timestamp_high_helper, read_timestamp_high));

        // adjusted constant contributions
        const e4 constant = (helpers++).get();
        denom = e4::add(denom, constant);
        const e4 e4_arg = stage_2_e4_cols.get_at_col(memory_args_start + flat_indirect_idx + i + 1);
        acc_quadratic = e4::add(acc_quadratic, e4::mul(e4_arg, denom));

        // flush result
        numerator = e4::add(numerator, constant);
        acc_quadratic = e4::sub(acc_quadratic, e4::mul(e4_arg_prev, numerator));
        e4_arg_prev = e4_arg;
      }
    }

    alphas += register_and_indirect_accesses.num_register_accesses + flat_indirect_idx;
  }

  {
    // kinda ugly with 3 e4 x e4 muls, but hopefully negligible overall
    const e4 memory_arg_entry = stage_2_e4_cols.get_at_col(memory_grand_product_col - 1);
    const e4 grand_product_entry = stage_2_e4_cols.get_at_col(memory_grand_product_col);
    e4 grand_product_entry_next{};
    if (gid == n - 1) {
      stage_2_e4_cols.sub_row(gid);
      grand_product_entry_next = stage_2_e4_cols.get_at_col(memory_grand_product_col);
      stage_2_e4_cols.add_row(gid);
    } else {
      stage_2_e4_cols.add_row(1);
      grand_product_entry_next = stage_2_e4_cols.get_at_col(memory_grand_product_col);
      stage_2_e4_cols.sub_row(1);
    }
    const e4 alpha = (alphas++).get();
    acc_linear = e4::add(acc_linear, e4::mul(alpha, grand_product_entry_next));
    const e4 prod = e4::mul(memory_arg_entry, grand_product_entry);
    acc_quadratic = e4::sub(acc_quadratic, e4::mul(alpha, prod));
  }

  // Finalize "every row except last" contributions
  acc_quadratic = e4::mul(acc_quadratic, decompression_factor_squared);
  acc_linear = e4::mul(acc_linear, decompression_factor);
  e4 acc = e4::add(acc_quadratic, acc_linear);
  const e4 current_quotient = quotient.get();
  acc = e4::add(acc, current_quotient);
  acc = e4::add(acc, constants_times_challenges->sum);
  const unsigned shift = 1 << (field::CIRCLE_GROUP_LOG_ORDER - log_n - 1);
  const e2 x = get_power_of_w(shift * (2 * gid + 1), false);
  const e2 num = e2::sub(x, omega_inv);
  e2 multiplier = e2::mul(num, every_row_zerofier);
  acc = e4::mul(acc, multiplier);
  // TODO: fold beta powers into corresponding alpha powers
  acc = e4::mul(acc, betas.get(5));

  // Constraints at every row except last two
  if (state_linkage_constraints.num_constraints > 0 || lazy_init_teardown_layout.process_shuffle_ram_init) {
    e4 acc_linear{e4::zero()};

    {
      auto witness_cols_next_row = witness_cols.copy();
      if (gid < n - 1)
        witness_cols_next_row.add_row(1);
      else
        witness_cols_next_row.sub_row(gid);

      for (unsigned i = 0; i < state_linkage_constraints.num_constraints; i++) {
        const e4 alpha = (alphas_every_row_except_last_two++).get();
        const bf src_val = witness_cols.get_at_col(state_linkage_constraints.srcs[i]);
        const bf dst_val = witness_cols_next_row.get_at_col(state_linkage_constraints.dsts[i]);
        acc_linear = e4::add(acc_linear, e4::mul(alpha, bf::sub(src_val, dst_val)));
      }
    }

    if (lazy_init_teardown_layout.process_shuffle_ram_init) {
      auto memory_cols_next_row = memory_cols.copy();
      if (gid < n - 1)
        memory_cols_next_row.add_row(1);
      else
        memory_cols_next_row.sub_row(gid);

      const bf intermediate_borrow = witness_cols.get_at_col(lazy_init_teardown_layout.init_address_intermediate_borrow);
      {
        const bf this_low = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start);
        const bf next_low = memory_cols_next_row.get_at_col(lazy_init_teardown_layout.init_address_start);
        const bf aux_low = witness_cols.get_at_col(lazy_init_teardown_layout.init_address_aux_low);
        bf tmp = bf::mul(SHIFT_16, intermediate_borrow);
        tmp = bf::add(tmp, this_low);
        tmp = bf::sub(tmp, next_low);
        tmp = bf::sub(tmp, aux_low);
        const e4 alpha = (alphas_every_row_except_last_two++).get();
        acc_linear = e4::add(acc_linear, e4::mul(alpha, tmp));
      }
      {
        const bf final_borrow = witness_cols.get_at_col(lazy_init_teardown_layout.init_address_final_borrow);
        const bf this_high = memory_cols.get_at_col(lazy_init_teardown_layout.init_address_start + 1);
        const bf next_high = memory_cols_next_row.get_at_col(lazy_init_teardown_layout.init_address_start + 1);
        const bf aux_high = witness_cols.get_at_col(lazy_init_teardown_layout.init_address_aux_high);
        bf tmp = bf::mul(SHIFT_16, final_borrow);
        tmp = bf::add(tmp, this_high);
        tmp = bf::sub(tmp, intermediate_borrow);
        tmp = bf::sub(tmp, next_high);
        tmp = bf::sub(tmp, aux_high);
        const e4 alpha = (alphas_every_row_except_last_two++).get();
        acc_linear = e4::add(acc_linear, e4::mul(alpha, tmp));
      }
    }

    // Finalize "every row except last two" contributions, which are purely linear
    acc_linear = e4::mul(acc_linear, decompression_factor);
    multiplier = e2::mul(multiplier, e2::sub(x, omega_inv_squared));
    acc_linear = e4::mul(acc_linear, multiplier);
    acc = e4::add(acc, e4::mul(betas.get(4), acc_linear));
  }

  const e2 denoms[4] = {x, e2::sub(x, bf::one()), e2::sub(x, omega_inv_squared), e2::sub(x, omega_inv)};
  e2 denom_invs[4] = {};
  batch_inv_registers<e2, 4, true>(denoms, denom_invs, 4);

  // Constraints at first row: grand product == 1, boundary constraints
  {
    e4 acc_linear = e4::mul((helpers++).get(), stage_2_e4_cols.get_at_col(memory_grand_product_col));
    unsigned i = 0;
    if (lazy_init_teardown_layout.process_shuffle_ram_init)
      for (; i < 6; i++)
        acc_linear = e4::add(acc_linear, e4::mul((helpers++).get(), memory_cols.get_at_col(boundary_constraints.first_row_cols[i])));
    for (; i < boundary_constraints.num_first_row; i++)
      acc_linear = e4::add(acc_linear, e4::mul((helpers++).get(), witness_cols.get_at_col(boundary_constraints.first_row_cols[i])));
    acc_linear = e4::add(acc_linear, constants_times_challenges->first_row);
    acc_linear = e4::mul(acc_linear, denom_invs[1]);
    acc = e4::add(acc, acc_linear);
  }

  // Boundary constraints at one before last row
  if (boundary_constraints.num_one_before_last_row > 0) {
    e4 acc_linear{};
    unsigned i = 0;
    if (lazy_init_teardown_layout.process_shuffle_ram_init) {
      acc_linear = e4::mul((helpers++).get(), memory_cols.get_at_col(boundary_constraints.one_before_last_row_cols[0]));
      i++;
      for (; i < 6; i++)
        acc_linear = e4::add(acc_linear, e4::mul((helpers++).get(), memory_cols.get_at_col(boundary_constraints.one_before_last_row_cols[i])));
    } else {
      acc_linear = e4::mul((helpers++).get(), witness_cols.get_at_col(boundary_constraints.one_before_last_row_cols[0]));
      i++;
    }
    for (; i < boundary_constraints.num_one_before_last_row; i++)
      acc_linear = e4::add(acc_linear, e4::mul((helpers++).get(), witness_cols.get_at_col(boundary_constraints.one_before_last_row_cols[i])));
    acc_linear = e4::add(acc_linear, constants_times_challenges->one_before_last_row);
    acc_linear = e4::mul(acc_linear, denom_invs[2]);
    acc = e4::add(acc, acc_linear);
  }

  // One constraint at last row (grand product accumulator)
  {
    e4 acc_linear = e4::mul((helpers++).get(), stage_2_e4_cols.get_at_col(memory_grand_product_col));
    acc_linear = e4::add(acc_linear, (helpers++).get());
    acc_linear = e4::mul(acc_linear, denom_invs[3]);
    acc = e4::add(acc, acc_linear);
  }

  // Constraints at last row and x = 0
  {
    e4 acc_linear = e4::neg(stage_2_e4_cols.get_at_col(range_check_16_multiplicities_layout.dst_cols_start));
    // validate col sums for range check 16 lookup e4 args
    {
      const unsigned num_range_check_16_e4_args = range_check_16_layout.num_dst_cols + expressions.num_range_check_16_expression_pairs;
      for (unsigned i = 0; i < num_range_check_16_e4_args; i++)
        acc_linear = e4::add(acc_linear, stage_2_e4_cols.get_at_col(range_check_16_layout.e4_args_start + i));
      if (lazy_init_teardown_layout.process_shuffle_ram_init)
        acc_linear = e4::add(acc_linear, stage_2_e4_cols.get_at_col(lazy_init_teardown_layout.e4_arg_col));
      acc_linear = e4::mul(acc_linear, (helpers++).get());
    }
    // validate col sums for timestamp range check e4 args
    if (timestamp_range_check_multiplicities_layout.num_dst_cols > 0) {
      e4 acc_timestamp = e4::neg(stage_2_e4_cols.get_at_col(timestamp_range_check_multiplicities_layout.dst_cols_start));
      const unsigned num_timestamp_e4_args = expressions.num_timestamp_expression_pairs + expressions_for_shuffle_ram.num_expression_pairs;
      // This start location and the contiguity of e4 args cols are checked on the Rust side.
      const unsigned start_e4_col = (expressions.num_timestamp_expression_pairs > 0) ? expressions.e4_dst_cols[expressions.num_range_check_16_expression_pairs]
                                                                                     : expressions_for_shuffle_ram.e4_dst_cols[0];
      for (unsigned i = 0; i < num_timestamp_e4_args; i++)
        acc_timestamp = e4::add(acc_timestamp, stage_2_e4_cols.get_at_col(start_e4_col + i));
      acc_timestamp = e4::mul(acc_timestamp, (helpers++).get());
      acc_linear = e4::add(acc_linear, acc_timestamp);
    }
    // validate col sums for generic lookup e4 args
    {
      e4 acc_generic = e4::neg(stage_2_e4_cols.get_at_col(generic_lookup_multiplicities_layout.dst_cols_start));
      for (unsigned i = 1; i < generic_lookup_multiplicities_layout.num_dst_cols; i++)
        acc_generic = e4::sub(acc_generic, stage_2_e4_cols.get_at_col(generic_lookup_multiplicities_layout.dst_cols_start + i));
      for (unsigned i = 0; i < width_3_lookups_layout.num_lookups; i++)
        acc_generic = e4::add(acc_generic, stage_2_e4_cols.get_at_col(width_3_lookups_layout.e4_arg_cols_start + i));
      acc_generic = e4::mul(acc_generic, (helpers++).get());
      acc_linear = e4::add(acc_linear, acc_generic);
    }
    if (handle_delegation_requests || process_delegations) {
      const e4 interpolant = e4::mul((helpers++).get(), x);
      const e4 e4_arg = stage_2_e4_cols.get_at_col(delegation_aux_poly_col);
      const e4 diff = e4::sub(e4_arg, interpolant);
      const e4 term = e4::mul(diff, (helpers++).get());
      acc_linear = e4::add(acc_linear, term);
    }
    const e2 denom_inv = e2::mul(denom_invs[0], denom_invs[3]);
    acc_linear = e4::mul(acc_linear, denom_inv);
    acc = e4::add(acc, acc_linear);
  }

  quotient.set(acc);
}
