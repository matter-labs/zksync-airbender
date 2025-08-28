#pragma once

#include "field.cuh"

using namespace ::airbender::field;

namespace airbender::arg_utils {

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef base_field bf;
typedef ext2_field e2;
typedef ext4_field e4;

constexpr unsigned NUM_DELEGATION_ARGUMENT_KEY_PARTS = 4;

struct DelegationChallenges {
  const e4 linearization_challenges[NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1];
  const e4 gamma;
};

struct DelegationRequestMetadata {
  const unsigned multiplicity_col;
  const unsigned timestamp_setup_col;
  const bf memory_timestamp_high_from_circuit_idx;
  const unsigned delegation_type_col;
  const unsigned abi_mem_offset_high_col;
  const bf in_cycle_write_idx;
};

struct DelegationProcessingMetadata {
  const unsigned multiplicity_col;
  const bf delegation_type;
  const unsigned abi_mem_offset_high_col;
  const unsigned write_timestamp_col;
};

constexpr unsigned NUM_LOOKUP_ARGUMENT_KEY_PARTS = 4;

struct LookupChallenges {
  const e4 linearization_challenges[NUM_LOOKUP_ARGUMENT_KEY_PARTS - 1];
  const e4 gamma;
};

struct RangeCheckArgsLayout {
  const unsigned num_dst_cols;
  const unsigned src_cols_start;
  const unsigned bf_args_start;
  const unsigned e4_args_start;
  // to be used if num_src_cols is odd, currently not supported on CPU
  // const unsigned maybe_e4_arg_remainder_col;
};

struct MemoryChallenges {
  const e4 address_low_challenge;
  const e4 address_high_challenge;
  const e4 timestamp_low_challenge;
  const e4 timestamp_high_challenge;
  const e4 value_low_challenge;
  const e4 value_high_challenge;
  const e4 gamma;
};

constexpr unsigned MAX_EXPRESSION_PAIRS = 84;
constexpr unsigned MAX_EXPRESSIONS = 2 * MAX_EXPRESSION_PAIRS;
constexpr unsigned MAX_TERMS_PER_EXPRESSION = 4;
constexpr unsigned MAX_EXPRESSION_TERMS = MAX_TERMS_PER_EXPRESSION * MAX_EXPRESSIONS;

struct FlattenedLookupExpressionsLayout {
  const unsigned coeffs[MAX_EXPRESSION_TERMS];
  const u16 col_idxs[MAX_EXPRESSION_TERMS];
  const bf constant_terms[MAX_EXPRESSIONS];
  const u8 num_terms_per_expression[MAX_EXPRESSIONS];
  const u8 bf_dst_cols[MAX_EXPRESSION_PAIRS];
  const u8 e4_dst_cols[MAX_EXPRESSION_PAIRS];
  const unsigned num_range_check_16_expression_pairs;
  const unsigned num_timestamp_expression_pairs;
  const bool range_check_16_constant_terms_are_zero;
  const bool timestamp_constant_terms_are_zero;
};

constexpr unsigned MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM = 4;
constexpr unsigned MAX_EXPRESSIONS_FOR_SHUFFLE_RAM = 2 * MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM;
constexpr unsigned MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM = MAX_TERMS_PER_EXPRESSION * MAX_EXPRESSIONS_FOR_SHUFFLE_RAM;

struct FlattenedLookupExpressionsForShuffleRamLayout {
  const unsigned coeffs[MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM];
  const u16 col_idxs[MAX_EXPRESSION_TERMS_FOR_SHUFFLE_RAM];
  const bf constant_terms[MAX_EXPRESSIONS_FOR_SHUFFLE_RAM];
  const u8 num_terms_per_expression[MAX_EXPRESSIONS_FOR_SHUFFLE_RAM];
  const u8 bf_dst_cols[MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM];
  const u8 e4_dst_cols[MAX_EXPRESSION_PAIRS_FOR_SHUFFLE_RAM];
  const unsigned num_expression_pairs;
};

// The top 2 bits of each u16 col index store the col type we're referring to.
constexpr unsigned COL_TYPE_MASK = 3 << 14;
constexpr unsigned COL_IDX_MASK = (1 << 14) - 1;
// don't mess an enum or enum class, avoid potential implicit conversions
constexpr unsigned COL_TYPE_WITNESS = 0;
constexpr unsigned COL_TYPE_MEMORY = 1 << 14;
constexpr unsigned COL_TYPE_SETUP = 1 << 15;

template <typename T, typename U> DEVICE_FORCEINLINE bf get_witness_or_memory(const unsigned col_idx, const T &witness_cols, const U &memory_cols) {
  return (col_idx & COL_TYPE_MEMORY) ? memory_cols.get_at_col(col_idx & COL_IDX_MASK) : witness_cols.get_at_col(col_idx);
}

template <typename T, typename U, typename V>
DEVICE_FORCEINLINE bf get_witness_memory_or_setup(const unsigned col_idx, const T &witness_cols, const U &memory_cols, const V &setup_cols) {
  const unsigned col_type = col_idx & COL_TYPE_MASK;
  bf val;
  switch (col_type) {
  case COL_TYPE_WITNESS:
    val = witness_cols.get_at_col(col_idx & COL_IDX_MASK);
    break;
  case COL_TYPE_MEMORY:
    val = memory_cols.get_at_col(col_idx & COL_IDX_MASK);
    break;
  case COL_TYPE_SETUP:
    val = setup_cols.get_at_col(col_idx & COL_IDX_MASK);
  default:
    break;
  }
  return val;
}

DEVICE_FORCEINLINE void apply_coeff(const unsigned coeff, bf &val) {
  switch (coeff) {
  case 1:
    break;
  case bf::MINUS_ONE:
    val = bf::neg(val);
    break;
  default:
    val = bf::mul(val, bf{coeff});
  }
}

template <bool APPLY_CONSTANT_TERMS, typename T>
DEVICE_FORCEINLINE void eval_a_and_b(bf a_and_b[2], const FlattenedLookupExpressionsLayout &expressions, unsigned &expression_idx, unsigned &flat_term_idx,
                                     const T &witness_cols, const T &memory_cols, const bool constant_terms_are_zero) {
#pragma unroll
  for (int j = 0; j < 2; j++, expression_idx++) {
    const unsigned lim = flat_term_idx + expressions.num_terms_per_expression[expression_idx];
    a_and_b[j] = get_witness_or_memory(expressions.col_idxs[flat_term_idx], witness_cols, memory_cols);
    apply_coeff(expressions.coeffs[flat_term_idx], a_and_b[j]);
    flat_term_idx++;
    for (; flat_term_idx < lim; flat_term_idx++) {
      bf val = get_witness_or_memory(expressions.col_idxs[flat_term_idx], witness_cols, memory_cols);
      apply_coeff(expressions.coeffs[flat_term_idx], val);
      a_and_b[j] = bf::add(a_and_b[j], val);
    }
    if (APPLY_CONSTANT_TERMS && !constant_terms_are_zero) {
      a_and_b[j] = bf::add(a_and_b[j], expressions.constant_terms[expression_idx]);
    }
  }
}

template <bool APPLY_CONSTANT_TERMS, typename T, typename U>
DEVICE_FORCEINLINE void eval_a_and_b(bf a_and_b[2], const FlattenedLookupExpressionsForShuffleRamLayout &expressions, unsigned &expression_idx,
                                     unsigned &flat_term_idx, const T &setup_cols, const U &witness_cols, const U &memory_cols) {
#pragma unroll
  for (int j = 0; j < 2; j++, expression_idx++) {
    const unsigned lim = flat_term_idx + expressions.num_terms_per_expression[expression_idx];
    a_and_b[j] = get_witness_memory_or_setup(expressions.col_idxs[flat_term_idx], witness_cols, memory_cols, setup_cols);
    apply_coeff(expressions.coeffs[flat_term_idx], a_and_b[j]);
    flat_term_idx++;
    for (; flat_term_idx < lim; flat_term_idx++) {
      const unsigned col = expressions.col_idxs[flat_term_idx];
      bf val = get_witness_memory_or_setup(col, witness_cols, memory_cols, setup_cols);
      apply_coeff(expressions.coeffs[flat_term_idx], val);
      a_and_b[j] = bf::add(a_and_b[j], val);
    }
    if (APPLY_CONSTANT_TERMS) {
      a_and_b[j] = bf::add(a_and_b[j], expressions.constant_terms[expression_idx]);
    }
  }
}

struct LazyInitTeardownLayout {
  const unsigned init_address_start;
  const unsigned teardown_value_start;
  const unsigned teardown_timestamp_start;
  const unsigned init_address_aux_low;
  const unsigned init_address_aux_high;
  const unsigned init_address_intermediate_borrow;
  const unsigned init_address_final_borrow;
  const unsigned bf_arg_col;
  const unsigned e4_arg_col;
  const bool process_shuffle_ram_init;
};

constexpr unsigned MAX_SHUFFLE_RAM_ACCESSES = 3;

struct ShuffleRamAccess {
  const unsigned address_start;
  const unsigned read_timestamp_start;
  const unsigned read_value_start;
  const unsigned maybe_write_value_start;
  const unsigned maybe_is_register_start;
  const bool is_write;
  const bool is_register_only;
};

struct ShuffleRamAccesses {
  const ShuffleRamAccess accesses[MAX_SHUFFLE_RAM_ACCESSES];
  const unsigned num_accesses;
  const unsigned write_timestamp_in_setup_start;
};

constexpr unsigned MAX_BATCHED_RAM_ACCESSES = 36;

struct BatchedRamAccess {
  const e4 gamma_plus_address_low_contribution;
  const unsigned read_timestamp_col;
  const unsigned read_value_col;
  const unsigned maybe_write_value_col;
  const bool is_write;
};

struct BatchedRamAccesses {
  const BatchedRamAccess accesses[MAX_BATCHED_RAM_ACCESSES];
  const unsigned num_accesses;
  const unsigned write_timestamp_col;
  const unsigned abi_mem_offset_high_col;
};

struct RegisterAccess {
  const e4 gamma_plus_one_plus_address_low_contribution;
  const unsigned read_timestamp_col;
  const unsigned read_value_col;
  const unsigned maybe_write_value_col;
  const bool is_write;
};

struct IndirectAccess {
  const unsigned offset;
  const unsigned read_timestamp_col;
  const unsigned read_value_col;
  const unsigned maybe_write_value_col;
  const unsigned address_derivation_carry_bit_col;
  const unsigned address_derivation_carry_bit_num_elements;
  const bool is_write;
};

constexpr unsigned MAX_REGISTER_ACCESSES = 4;
constexpr unsigned MAX_INDIRECT_ACCESSES = 40;

struct RegisterAndIndirectAccesses {
  const RegisterAccess register_accesses[MAX_REGISTER_ACCESSES];
  const IndirectAccess indirect_accesses[MAX_INDIRECT_ACCESSES];
  const unsigned indirect_accesses_per_register_access[MAX_REGISTER_ACCESSES];
  const unsigned num_register_accesses;
  const unsigned write_timestamp_col;
};

} // namespace airbender::arg_utils