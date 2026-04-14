#pragma once

#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::prover::gkr {

enum gkr_base_source_kind : u32 {
  GKR_BASE_SOURCE_EMPTY = 0,
  GKR_BASE_SOURCE_REAL = 1,
  GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS = 2,
  GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP = 3,
  GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW = 4,
  GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH = 5,
};

template <typename E> struct gkr_ext_initial_source {
  const E *start;
  size_t next_layer_size;
};

template <typename B> struct gkr_base_initial_source {
  const B *start;
  size_t next_layer_size;
  gkr_base_source_kind source_kind;
};

template <typename B, typename E> struct gkr_base_after_one_source {
  size_t base_layer_half_size;
  size_t next_layer_size;
  const B *base_input_start;
  E *this_layer_cache_start;
  bool first_access;
  gkr_base_source_kind source_kind;
};

template <typename B, typename E> struct gkr_base_after_two_source {
  const B *base_input_start;
  E *this_layer_cache_start;
  size_t base_layer_half_size;
  size_t base_quarter_size;
  size_t next_layer_size;
  bool first_access;
  gkr_base_source_kind source_kind;
};

template <typename E> struct gkr_ext_continuing_source {
  const E *previous_layer_start;
  E *this_layer_start;
  size_t this_layer_size;
  size_t next_layer_size;
  bool first_access;
};

template <typename E> struct gkr_main_constraint_quadratic_term {
  u32 lhs;
  u32 rhs;
  E challenge;
};

template <typename E> struct gkr_main_constraint_linear_term {
  u32 input;
  E challenge;
};

enum gkr_main_kernel_kind : u32 {
  GKR_MAIN_BASE_COPY = 0,
  GKR_MAIN_EXT_COPY = 1,
  GKR_MAIN_PRODUCT = 2,
  GKR_MAIN_MASK_IDENTITY = 3,
  GKR_MAIN_LOOKUP_PAIR = 4,
  GKR_MAIN_LOOKUP_BASE_PAIR = 5,
  GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY = 6,
  GKR_MAIN_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT = 7,
  GKR_MAIN_LOOKUP_UNBALANCED = 8,
  GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP = 9,
  GKR_MAIN_ENFORCE_CONSTRAINTS = 10,
  GKR_MAIN_LINEAR_BASE_OUTPUT = 11,
  GKR_MAIN_INITS_AND_TEARDOWNS_INITIAL_PAIR = 12,
  GKR_MAIN_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES = 13,
  GKR_MAIN_MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION = 14,
  GKR_MAIN_LOOKUP_PAIR_FROM_BASE_INPUTS = 15,
  GKR_MAIN_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS = 16,
  GKR_MAIN_LOOKUP_PAIR_FROM_VECTOR_INPUTS = 17,
  GKR_MAIN_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP = 18,
  GKR_MAIN_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS = 19,
  GKR_MAIN_LOOKUP_EXT_PAIR = 20,
  GKR_MAIN_LOOKUP_UNBALANCED_EXTENSION = 21,
};

static constexpr unsigned GKR_FORWARD_MAX_GATES_PER_LAYER = 63;
static constexpr unsigned GKR_BACKWARD_MAX_KERNELS_PER_LAYER = 64;
static constexpr unsigned GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES = 12 * 1024;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_MAX_INPUTS = 5;
static constexpr unsigned GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS = 10;
static constexpr unsigned GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK = 512;
static constexpr unsigned GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK = 4;
static constexpr unsigned GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE = 32;
static constexpr unsigned GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK = GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK / GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE;
static constexpr unsigned GKR_EQ_GROUP_SIZE = 8;
static constexpr unsigned GKR_EQ_GROUP_TABLE_LEN = 1u << GKR_EQ_GROUP_SIZE;
static constexpr unsigned GKR_EQ_CHUNK_SIZE = 2;
static constexpr unsigned GKR_EQ_CHUNK_TABLE_LEN = 1u << GKR_EQ_CHUNK_SIZE;
static constexpr unsigned GKR_EQ_MAX_CHUNKS_PER_GROUP = GKR_EQ_GROUP_SIZE / GKR_EQ_CHUNK_SIZE;

enum gkr_main_batch_record_mode : u32 {
  GKR_MAIN_BATCH_INLINE_ALL = 0,
  GKR_MAIN_BATCH_INLINE_NO_METADATA = 1,
  GKR_MAIN_BATCH_POINTER_DESCRIPTORS = 2,
};

struct gkr_main_payload_range {
  u32 offset;
  u32 count;
};

template <typename E> struct gkr_main_constraint_metadata_device_pointers {
  const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
  u32 quadratic_terms_count;
  const gkr_main_constraint_linear_term<E> *linear_terms;
  u32 linear_terms_count;
  const E *constant_offset;
};

template <typename E> struct gkr_main_round0_batch_record {
  u32 kind;
  u32 record_mode;
  u32 metadata_inline;
  u32 reserved;
  gkr_main_payload_range base_inputs;
  gkr_main_payload_range extension_inputs;
  gkr_main_payload_range base_outputs;
  gkr_main_payload_range extension_outputs;
  gkr_main_payload_range quadratic_terms;
  gkr_main_payload_range linear_terms;
  E auxiliary_challenge;
  E constant_offset;
};

template <typename E> struct gkr_main_round1_batch_record {
  u32 kind;
  u32 record_mode;
  u32 metadata_inline;
  u32 reserved;
  gkr_main_payload_range base_inputs;
  gkr_main_payload_range extension_inputs;
  gkr_main_payload_range quadratic_terms;
  gkr_main_payload_range linear_terms;
  E auxiliary_challenge;
  E constant_offset;
};

template <typename E> struct gkr_main_round2_batch_record {
  u32 kind;
  u32 record_mode;
  u32 metadata_inline;
  u32 reserved;
  gkr_main_payload_range base_inputs;
  gkr_main_payload_range extension_inputs;
  gkr_main_payload_range quadratic_terms;
  gkr_main_payload_range linear_terms;
  E auxiliary_challenge;
  E constant_offset;
};

template <typename E> struct gkr_main_round3_batch_record {
  u32 kind;
  u32 record_mode;
  u32 metadata_inline;
  u32 reserved;
  gkr_main_payload_range base_inputs;
  gkr_main_payload_range extension_inputs;
  gkr_main_payload_range quadratic_terms;
  gkr_main_payload_range linear_terms;
  E auxiliary_challenge;
  E constant_offset;
};

template <typename E> struct gkr_main_round0_batch_static {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  gkr_main_round0_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_main_round0_batch_runtime {
  const E *eq_values;
  const E *batch_challenges;
  E *contributions;
  const u8 *spill_payload;
  const E *auxiliary_challenges;
  const gkr_main_constraint_metadata_device_pointers<E> *constraint_metadata;
};

template <typename E> struct gkr_main_round1_batch_static {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  gkr_main_round1_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_main_round1_batch_runtime {
  const E *eq_values;
  const E *batch_challenges;
  const E *folding_challenge;
  E *contributions;
  const u8 *spill_payload;
  const E *auxiliary_challenges;
  const gkr_main_constraint_metadata_device_pointers<E> *constraint_metadata;
};

template <typename E> struct gkr_main_round2_batch_static {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  gkr_main_round2_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_main_round2_batch_runtime {
  const E *eq_values;
  const E *batch_challenges;
  const E *folding_challenges;
  E *contributions;
  const u8 *spill_payload;
  const E *auxiliary_challenges;
  const gkr_main_constraint_metadata_device_pointers<E> *constraint_metadata;
};

template <typename E> struct gkr_main_round3_batch_static {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  gkr_main_round3_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_main_round3_batch_runtime {
  const E *eq_values;
  const E *batch_challenges;
  const E *folding_challenge;
  E *contributions;
  const u8 *spill_payload;
  const E *auxiliary_challenges;
  const gkr_main_constraint_metadata_device_pointers<E> *constraint_metadata;
};

DEVICE_FORCEINLINE bool gkr_main_batch_descriptors_inline(const u32 record_mode) { return record_mode != GKR_MAIN_BATCH_POINTER_DESCRIPTORS; }

template <typename T, typename Batch>
DEVICE_FORCEINLINE const T *gkr_main_batch_payload_ptr(const Batch &batch, const gkr_main_payload_range &range, const bool from_inline) {
  if (range.count == 0)
    return nullptr;
  const u8 *base = from_inline ? batch.inline_payload : batch.spill_payload;
  return reinterpret_cast<const T *>(base + range.offset);
}

template <typename T, typename Batch>
DEVICE_FORCEINLINE const T *gkr_main_batch_payload_ptr(const Batch &batch, const u8 *spill_payload, const gkr_main_payload_range &range,
                                                       const bool from_inline) {
  if (range.count == 0)
    return nullptr;
  const u8 *base = from_inline ? batch.inline_payload : spill_payload;
  return reinterpret_cast<const T *>(base + range.offset);
}

template <typename E> DEVICE_FORCEINLINE const E *gkr_main_batch_challenges(const E *batch_challenge_base, const u32 offset, const u32 count, E (&storage)[2]) {
  storage[0] = E::ZERO();
  storage[1] = E::ZERO();
  if (count == 0)
    return storage;
  E current = E::pow(*batch_challenge_base, offset);
  for (u32 i = 0; i < count && i < 2; ++i) {
    storage[i] = current;
    current = E::mul(current, *batch_challenge_base);
  }
  return storage;
}

DEVICE_FORCEINLINE unsigned gkr_main_kind_batch_challenge_count(const u32 kind) {
  switch (kind) {
  case GKR_MAIN_LOOKUP_PAIR:
  case GKR_MAIN_LOOKUP_BASE_PAIR:
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY:
  case GKR_MAIN_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT:
  case GKR_MAIN_LOOKUP_UNBALANCED:
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP:
  case GKR_MAIN_LOOKUP_PAIR_FROM_BASE_INPUTS:
  case GKR_MAIN_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS:
  case GKR_MAIN_LOOKUP_PAIR_FROM_VECTOR_INPUTS:
  case GKR_MAIN_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP:
  case GKR_MAIN_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS:
  case GKR_MAIN_LOOKUP_EXT_PAIR:
  case GKR_MAIN_LOOKUP_UNBALANCED_EXTENSION:
    return 2;
  default:
    return 1;
  }
}

template <typename E, typename Batch, typename Record>
DEVICE_FORCEINLINE void gkr_main_batch_constraint_metadata(const Batch &batch, const u8 *spill_payload, const Record &record,
                                                           const gkr_main_constraint_metadata_device_pointers<E> *runtime_metadata,
                                                           const gkr_main_constraint_quadratic_term<E> *&quadratic_terms, unsigned &quadratic_terms_count,
                                                           const gkr_main_constraint_linear_term<E> *&linear_terms, unsigned &linear_terms_count,
                                                           E &constant_offset) {
  if (runtime_metadata != nullptr) {
    quadratic_terms = runtime_metadata->quadratic_terms;
    quadratic_terms_count = runtime_metadata->quadratic_terms_count;
    linear_terms = runtime_metadata->linear_terms;
    linear_terms_count = runtime_metadata->linear_terms_count;
    constant_offset = runtime_metadata->constant_offset == nullptr ? E::ZERO() : *runtime_metadata->constant_offset;
    if (quadratic_terms != nullptr || linear_terms != nullptr || runtime_metadata->constant_offset != nullptr)
      return;
  }
  const bool metadata_inline = record.metadata_inline != 0;
  quadratic_terms = gkr_main_batch_payload_ptr<gkr_main_constraint_quadratic_term<E>>(batch, spill_payload, record.quadratic_terms, metadata_inline);
  quadratic_terms_count = record.quadratic_terms.count;
  linear_terms = gkr_main_batch_payload_ptr<gkr_main_constraint_linear_term<E>>(batch, spill_payload, record.linear_terms, metadata_inline);
  linear_terms_count = record.linear_terms.count;
  constant_offset = record.constant_offset;
}

enum gkr_dim_reducing_kernel_kind : u32 {
  GKR_DIM_REDUCING_PAIRWISE = 0,
  GKR_DIM_REDUCING_LOOKUP = 1,
};

enum gkr_dim_reducing_batch_record_mode : u32 {
  GKR_DIM_REDUCING_BATCH_INLINE_DESCRIPTORS = 0,
  GKR_DIM_REDUCING_BATCH_POINTER_DESCRIPTORS = 1,
};

struct gkr_dim_reducing_round0_batch_record {
  u32 kind;
  u32 record_mode;
  u32 reserved0;
  u32 reserved1;
  gkr_main_payload_range extension_inputs;
  gkr_main_payload_range extension_outputs;
  u32 batch_challenge_offset;
  u32 batch_challenge_count;
};

struct gkr_dim_reducing_continuation_batch_record {
  u32 kind;
  u32 record_mode;
  u32 reserved0;
  u32 reserved1;
  gkr_main_payload_range extension_inputs;
  u32 batch_challenge_offset;
  u32 batch_challenge_count;
};

template <typename E> struct gkr_dim_reducing_round0_batch {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  const E *eq_values;
  const E *batch_challenge_base;
  E *contributions;
  const u8 *spill_payload;
  gkr_dim_reducing_round0_batch_record records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_dim_reducing_round1_batch {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  const E *eq_values;
  const E *batch_challenge_base;
  const E *folding_challenge;
  E *contributions;
  const u8 *spill_payload;
  bool explicit_form;
  u8 padding[7];
  gkr_dim_reducing_continuation_batch_record records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_dim_reducing_round2_batch {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  const E *eq_values;
  const E *batch_challenge_base;
  const E *folding_challenge;
  E *contributions;
  const u8 *spill_payload;
  bool explicit_form;
  u8 padding[7];
  gkr_dim_reducing_continuation_batch_record records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_dim_reducing_round3_batch {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  const E *eq_values;
  const E *batch_challenge_base;
  const E *folding_challenge;
  E *contributions;
  const u8 *spill_payload;
  bool explicit_form;
  u8 padding[7];
  gkr_dim_reducing_continuation_batch_record records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

DEVICE_FORCEINLINE bool gkr_dim_reducing_batch_descriptors_inline(const u32 record_mode) { return record_mode == GKR_DIM_REDUCING_BATCH_INLINE_DESCRIPTORS; }

constexpr unsigned GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS = 8;

enum gkr_forward_cache_address_space_kind : u32 {
  GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY = 0,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT = 1,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_IS = 2,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT = 3,
};

enum gkr_forward_gate_kind : u32 {
  GKR_FORWARD_NO_OP = 0,
  GKR_FORWARD_PRODUCT = 1,
  GKR_FORWARD_MASK_IDENTITY = 2,
  GKR_FORWARD_LOOKUP_PAIR = 3,
  GKR_FORWARD_LOOKUP_WITH_CACHED_DENS_AND_SETUP = 4,
  GKR_FORWARD_LOOKUP_BASE_PAIR = 5,
  GKR_FORWARD_LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE = 6,
  GKR_FORWARD_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT = 7,
  GKR_FORWARD_LOOKUP_UNBALANCED_BASE = 8,
  GKR_FORWARD_LOOKUP_UNBALANCED_EXTENSION = 9,
  GKR_FORWARD_LOOKUP_EXT_PAIR = 10,
  GKR_FORWARD_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES = 11,
  GKR_FORWARD_MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION = 12,
  GKR_FORWARD_LOOKUP_PAIR_FROM_BASE_INPUTS = 13,
  GKR_FORWARD_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS = 14,
  GKR_FORWARD_LOOKUP_PAIR_FROM_VECTOR_INPUTS = 15,
  GKR_FORWARD_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP = 16,
  GKR_FORWARD_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS = 17,
};

struct gkr_forward_no_op_descriptor {
  size_t reserved;
};

template <typename E> struct gkr_forward_product_descriptor {
  const E *lhs;
  const E *rhs;
  E *dst;
};

template <typename E> struct gkr_forward_mask_identity_descriptor {
  const E *input;
  const bf *mask;
  E *dst;
};

template <typename E> struct gkr_forward_lookup_pair_descriptor {
  const E *a;
  const E *b;
  const E *c;
  const E *d;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_with_cached_dens_and_setup_descriptor {
  const bf *a;
  const E *b;
  const bf *c;
  const E *d;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_base_pair_descriptor {
  const bf *lhs;
  const bf *rhs;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_ext_pair_descriptor {
  const E *lhs;
  const E *rhs;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_base_minus_multiplicity_by_base_descriptor {
  const bf *b;
  const bf *c;
  const bf *d;
  gkr_base_source_kind d_source_kind;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_ext_minus_multiplicity_by_ext_descriptor {
  const E *b;
  const bf *c;
  const E *d;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_unbalanced_base_descriptor {
  const E *a;
  const E *b;
  const bf *remainder;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_unbalanced_extension_descriptor {
  const E *a;
  const E *b;
  const E *remainder;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_memory_tuple_expression_descriptor {
  gkr_forward_cache_address_space_kind address_space_kind;
  const bf *address_space_ptr;
  bf address_space_constant;
  E constant_term;
  const bf *linear_inputs[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
  E linear_challenges[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
};

template <typename E> struct gkr_forward_initial_grand_product_without_caches_descriptor {
  gkr_forward_memory_tuple_expression_descriptor<E> lhs;
  gkr_forward_memory_tuple_expression_descriptor<E> rhs;
  E *dst;
};

template <typename E> struct gkr_forward_materialize_grand_product_term_expression_descriptor {
  gkr_forward_memory_tuple_expression_descriptor<E> input;
  E *dst;
};

template <typename E> struct gkr_forward_lookup_pair_from_base_inputs_descriptor {
  const u32 *lhs_mapping;
  const u32 *rhs_mapping;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_with_dens_and_setup_expressions_descriptor {
  const bf *decoder_predicate;
  const u32 *input_mapping;
  const bf *multiplicity;
  const E *generic_lookup;
  const E *decoder_fill_value;
  u32 generic_lookup_len;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_pair_from_vector_inputs_descriptor {
  const u32 *lhs_mapping;
  const u32 *rhs_mapping;
  const E *generic_lookup;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_from_vector_input_with_setup_descriptor {
  const u32 *input_mapping;
  const bf *multiplicity;
  const E *generic_lookup;
  u32 generic_lookup_len;
  E *num;
  E *den;
};

template <typename E> struct gkr_forward_lookup_unbalanced_pair_with_vector_inputs_descriptor {
  const E *a;
  const E *b;
  const u32 *remainder_mapping;
  const E *generic_lookup;
  E *num;
  E *den;
};

template <typename E> union gkr_forward_gate_payload {
  gkr_forward_no_op_descriptor no_op;
  gkr_forward_product_descriptor<E> product;
  gkr_forward_mask_identity_descriptor<E> mask_identity;
  gkr_forward_lookup_pair_descriptor<E> lookup_pair;
  gkr_forward_lookup_with_cached_dens_and_setup_descriptor<E> lookup_with_cached_dens_and_setup;
  gkr_forward_lookup_base_pair_descriptor<E> lookup_base_pair;
  gkr_forward_lookup_ext_pair_descriptor<E> lookup_ext_pair;
  gkr_forward_lookup_base_minus_multiplicity_by_base_descriptor<E> lookup_base_minus_multiplicity_by_base;
  gkr_forward_lookup_ext_minus_multiplicity_by_ext_descriptor<E> lookup_ext_minus_multiplicity_by_ext;
  gkr_forward_lookup_unbalanced_base_descriptor<E> lookup_unbalanced_base;
  gkr_forward_lookup_unbalanced_extension_descriptor<E> lookup_unbalanced_extension;
  gkr_forward_initial_grand_product_without_caches_descriptor<E> initial_grand_product_without_caches;
  gkr_forward_materialize_grand_product_term_expression_descriptor<E> materialize_grand_product_term_expression;
  gkr_forward_lookup_pair_from_base_inputs_descriptor<E> lookup_pair_from_base_inputs;
  gkr_forward_lookup_with_dens_and_setup_expressions_descriptor<E> lookup_with_dens_and_setup_expressions;
  gkr_forward_lookup_pair_from_vector_inputs_descriptor<E> lookup_pair_from_vector_inputs;
  gkr_forward_lookup_from_vector_input_with_setup_descriptor<E> lookup_from_vector_input_with_setup;
  gkr_forward_lookup_unbalanced_pair_with_vector_inputs_descriptor<E> lookup_unbalanced_pair_with_vector_inputs;
};

template <typename E> struct gkr_forward_gate_descriptor {
  u32 kind;
  u32 reserved;
  gkr_forward_gate_payload<E> payload;
};

template <typename E> struct gkr_forward_layer_batch {
  u32 gate_count;
  u32 reserved;
  const E *lookup_additive_challenge;
  gkr_forward_gate_descriptor<E> descriptors[GKR_FORWARD_MAX_GATES_PER_LAYER];
};

enum gkr_dim_reducing_forward_input_kind : u32 {
  GKR_DIM_REDUCING_FORWARD_NO_OP = 0,
  GKR_DIM_REDUCING_FORWARD_PAIRWISE_PRODUCT = 1,
  GKR_DIM_REDUCING_FORWARD_LOOKUP_PAIR = 2,
};

struct gkr_dim_reducing_forward_no_op_descriptor {
  size_t reserved;
};

template <typename E> struct gkr_dim_reducing_forward_pairwise_product_descriptor {
  const E *input;
  E *output;
};

template <typename E> struct gkr_dim_reducing_forward_lookup_pair_descriptor {
  const E *num;
  const E *den;
  E *output_num;
  E *output_den;
};

template <typename E> union gkr_dim_reducing_forward_input_payload {
  gkr_dim_reducing_forward_no_op_descriptor no_op;
  gkr_dim_reducing_forward_pairwise_product_descriptor<E> pairwise_product;
  gkr_dim_reducing_forward_lookup_pair_descriptor<E> lookup_pair;
};

template <typename E> struct gkr_dim_reducing_forward_input_descriptor {
  u32 kind;
  u32 reserved;
  gkr_dim_reducing_forward_input_payload<E> payload;
};

template <typename E> struct gkr_dim_reducing_forward_batch {
  u32 input_count;
  u32 reserved;
  gkr_dim_reducing_forward_input_descriptor<E> descriptors[GKR_DIM_REDUCING_FORWARD_MAX_INPUTS];
};

struct gkr_forward_setup_generic_lookup_descriptor {
  const bf *input;
};

template <typename E> struct gkr_forward_setup_generic_lookup_batch {
  u32 column_count;
  u32 reserved;
  const E *alpha_powers;
  E *output;
  gkr_forward_setup_generic_lookup_descriptor descriptors[GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
};

constexpr unsigned GKR_FORWARD_CACHE_MAX_RELATIONS = 20;

enum gkr_forward_cache_kind : u32 {
  GKR_FORWARD_CACHE_EMPTY = 0,
  GKR_FORWARD_CACHE_SINGLE_COLUMN_LOOKUP = 1,
  GKR_FORWARD_CACHE_VECTORIZED_LOOKUP = 2,
  GKR_FORWARD_CACHE_VECTORIZED_LOOKUP_SETUP = 3,
  GKR_FORWARD_CACHE_MEMORY_TUPLE = 4,
};

template <typename E> struct gkr_forward_cache_descriptor {
  gkr_forward_cache_kind kind;
  gkr_forward_cache_address_space_kind address_space_kind;
  const u32 *mapping;
  const bf *setup_values;
  gkr_base_source_kind setup_source_kind;
  const E *generic_lookup;
  const bf *decoder_mask;
  const E *decoder_fill_value;
  bf *base_output;
  E *ext_output;
  u32 generic_lookup_len;
  const bf *address_space_ptr;
  bf address_space_constant;
  E constant_term;
  const bf *linear_inputs[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
  E linear_challenges[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
};

template <typename E> struct gkr_forward_cache_batch {
  u32 count;
  gkr_forward_cache_descriptor<E> descriptors[GKR_FORWARD_CACHE_MAX_RELATIONS];
};

static constexpr unsigned GKR_TIMESTAMP_COLUMNS_NUM_BITS = 19;

DEVICE_FORCEINLINE bf gkr_virtual_base_value(const gkr_base_source_kind kind, const unsigned row) {
  switch (kind) {
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS:
    return row < (1u << 16) ? bf::from_canonical_u32(row) : bf::ZERO();
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP:
    return row < (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS) ? bf::from_canonical_u32(row) : bf::ZERO();
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW:
    return bf::from_canonical_u32((row << 2) & 0xffffu);
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH:
    return bf::from_canonical_u32(row >> 14);
  case GKR_BASE_SOURCE_EMPTY:
  case GKR_BASE_SOURCE_REAL:
  default:
    return bf::ZERO();
  }
}

template <typename E> DEVICE_FORCEINLINE void gkr_forward_cache_memory_tuple(const gkr_forward_cache_descriptor<E> &descriptor, const unsigned gid) {
  E value = descriptor.constant_term;
  switch (descriptor.address_space_kind) {
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT:
    value = E::add(value, descriptor.address_space_constant);
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_IS:
    value = E::add(value, load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT:
    value = E::add(value, E::sub(E::ONE(), load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid)));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY:
    break;
  }

#pragma unroll
  for (unsigned term = 0; term < GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS; ++term) {
    if (descriptor.linear_inputs[term] == nullptr)
      continue;
    const bf input = load<bf, ld_modifier::cs>(descriptor.linear_inputs[term], gid);
    value = E::add(value, E::mul(descriptor.linear_challenges[term], input));
  }

  store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_forward_memory_tuple_value(const gkr_forward_memory_tuple_expression_descriptor<E> &descriptor, const unsigned gid) {
  E value = descriptor.constant_term;
  switch (descriptor.address_space_kind) {
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT:
    value = E::add(value, descriptor.address_space_constant);
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_IS:
    value = E::add(value, load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT:
    value = E::add(value, E::sub(E::ONE(), load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid)));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY:
    break;
  }

#pragma unroll
  for (unsigned term = 0; term < GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS; ++term) {
    if (descriptor.linear_inputs[term] == nullptr)
      continue;
    const bf input = load<bf, ld_modifier::cs>(descriptor.linear_inputs[term], gid);
    value = E::add(value, E::mul(descriptor.linear_challenges[term], input));
  }

  return value;
}

template <typename E> DEVICE_FORCEINLINE E gkr_forward_lookup_setup_value(const E *generic_lookup, const u32 generic_lookup_len, const unsigned gid) {
  return gid < generic_lookup_len ? load<E, ld_modifier::cs>(generic_lookup, gid) : E::ZERO();
}

template <typename E> DEVICE_FORCEINLINE void gkr_forward_cache(const gkr_forward_cache_batch<E> &batch, const unsigned trace_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= trace_len)
    return;

#pragma unroll
  for (unsigned relation_idx = 0; relation_idx < GKR_FORWARD_CACHE_MAX_RELATIONS; ++relation_idx) {
    if (relation_idx >= batch.count)
      return;

    const auto &descriptor = batch.descriptors[relation_idx];
    switch (descriptor.kind) {
    case GKR_FORWARD_CACHE_SINGLE_COLUMN_LOOKUP: {
      const unsigned mapping = descriptor.mapping[gid];
      const bf value = descriptor.setup_source_kind == GKR_BASE_SOURCE_REAL ? load<bf, ld_modifier::cs>(descriptor.setup_values, mapping)
                                                                            : gkr_virtual_base_value(descriptor.setup_source_kind, mapping);
      store<bf, st_modifier::cs>(descriptor.base_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_VECTORIZED_LOOKUP: {
      const unsigned mapping = descriptor.mapping[gid];
      E value = load<E, ld_modifier::cs>(descriptor.generic_lookup, mapping);
      if (descriptor.decoder_mask != nullptr) {
        const bf enabled = load<bf, ld_modifier::cs>(descriptor.decoder_mask, gid);
        if (enabled.limb == 0) {
          value = load<E, ld_modifier::cs>(descriptor.decoder_fill_value, 0);
        }
      }
      store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_VECTORIZED_LOOKUP_SETUP: {
      const E value = gid < descriptor.generic_lookup_len ? load<E, ld_modifier::cs>(descriptor.generic_lookup, gid) : E::ZERO();
      store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_MEMORY_TUPLE:
      gkr_forward_cache_memory_tuple(descriptor, gid);
      break;
    case GKR_FORWARD_CACHE_EMPTY:
      return;
    }
  }
}

template <typename E>
DEVICE_FORCEINLINE bf gkr_get_forward_lookup_base_setup_value(const gkr_forward_lookup_base_minus_multiplicity_by_base_descriptor<E> &params,
                                                              const unsigned gid) {
  return params.d_source_kind == GKR_BASE_SOURCE_REAL ? load<bf, ld_modifier::cs>(params.d, gid) : gkr_virtual_base_value(params.d_source_kind, gid);
}

DEVICE_FORCEINLINE bf gkr_get_initial_base_bf_value(const gkr_base_initial_source<bf> &source, const unsigned index) {
  if (source.source_kind == GKR_BASE_SOURCE_REAL)
    return load<bf, ld_modifier::cs>(source.start, index);
  return gkr_virtual_base_value(source.source_kind, index);
}

template <typename E> DEVICE_FORCEINLINE bf gkr_get_base_after_one_bf_value(const gkr_base_after_one_source<bf, E> &source, const unsigned index) {
  if (source.source_kind == GKR_BASE_SOURCE_REAL)
    return load<bf, ld_modifier::cs>(source.base_input_start, index);
  return gkr_virtual_base_value(source.source_kind, index);
}

template <typename E> DEVICE_FORCEINLINE bf gkr_get_base_after_two_bf_value(const gkr_base_after_two_source<bf, E> &source, const unsigned index) {
  if (source.source_kind == GKR_BASE_SOURCE_REAL)
    return load<bf, ld_modifier::cs>(source.base_input_start, index);
  return gkr_virtual_base_value(source.source_kind, index);
}

DEVICE_FORCEINLINE bf gkr_get_initial_base_value(const gkr_base_initial_source<bf> &source, const unsigned index) {
  return gkr_get_initial_base_bf_value(source, index);
}

DEVICE_FORCEINLINE bf gkr_get_initial_base_delta(const gkr_base_initial_source<bf> &source, const unsigned index) {
  const bf f0 = gkr_get_initial_base_bf_value(source, index);
  const bf f1 = gkr_get_initial_base_bf_value(source, source.next_layer_size + index);
  return bf::sub(f1, f0);
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_value(const gkr_ext_initial_source<E> &source, const unsigned index) {
  return load<E, ld_modifier::cs>(source.start, index);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_continuing_value(const gkr_ext_continuing_source<E> &source, const E folding_challenge, const unsigned index) {
  if (!source.first_access)
    return load<E, ld_modifier::cs>(source.this_layer_start, index);

  const E f0 = load<E, ld_modifier::cs>(source.previous_layer_start, index);
  const E f1 = load<E, ld_modifier::cs>(source.previous_layer_start, source.this_layer_size + index);
  const E diff = E::sub(f1, f0);
  const E folded = E::add(f0, E::mul(folding_challenge, diff));
  store<E, st_modifier::cs>(source.this_layer_start, folded, index);
  return folded;
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_delta(const gkr_ext_initial_source<E> &source, const unsigned index) {
  const E f0 = gkr_get_initial_value(source, index);
  const E f1 = gkr_get_initial_value(source, source.next_layer_size + index);
  return E::sub(f1, f0);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_base_after_one_value(const gkr_base_after_one_source<bf, E> &source, const E first_folding_challenge, const unsigned index) {
  if (!source.first_access)
    return load<E, ld_modifier::cs>(source.this_layer_cache_start, index);

  const bf f0 = gkr_get_base_after_one_bf_value(source, index);
  const bf f1 = gkr_get_base_after_one_bf_value(source, source.base_layer_half_size + index);
  const bf diff = bf::sub(f1, f0);
  const E folded = E::add(E::mul(first_folding_challenge, diff), f0);
  store<E, st_modifier::cs>(source.this_layer_cache_start, folded, index);
  return folded;
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_get_base_after_one_points(const gkr_base_after_one_source<bf, E> &source, const E first_folding_challenge, const unsigned index,
                                                      E &f0, E &f1_or_delta) {
  f0 = gkr_get_base_after_one_value(source, first_folding_challenge, index);
  const E f1 = gkr_get_base_after_one_value(source, first_folding_challenge, source.next_layer_size + index);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E>
DEVICE_FORCEINLINE E gkr_get_base_after_two_value(const gkr_base_after_two_source<bf, E> &source, const E first_folding_challenge,
                                                  const E second_folding_challenge, const unsigned index) {
  if (!source.first_access)
    return load<E, ld_modifier::cs>(source.this_layer_cache_start, index);

  const bf f00 = gkr_get_base_after_two_bf_value(source, index);
  const bf f01 = gkr_get_base_after_two_bf_value(source, source.base_layer_half_size + index);
  const bf f10 = gkr_get_base_after_two_bf_value(source, source.base_quarter_size + index);
  const bf f11 = gkr_get_base_after_two_bf_value(source, source.base_layer_half_size + source.base_quarter_size + index);

  const bf c01 = bf::sub(f01, f00);
  const bf c10 = bf::sub(f10, f00);
  bf c11 = f00;
  c11 = bf::sub(c11, f01);
  c11 = bf::sub(c11, f10);
  c11 = bf::add(c11, f11);

  E combined_challenges = E::mul(first_folding_challenge, second_folding_challenge);
  E result = E::mul(first_folding_challenge, c01);
  result = E::add(result, E::mul(second_folding_challenge, c10));
  result = E::add(result, E::mul(combined_challenges, c11));
  result = E::add(result, f00);

  store<E, st_modifier::cs>(source.this_layer_cache_start, result, index);
  return result;
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_get_base_after_two_points(const gkr_base_after_two_source<bf, E> &source, const E first_folding_challenge,
                                                      const E second_folding_challenge, const unsigned index, E &f0, E &f1_or_delta) {
  f0 = gkr_get_base_after_two_value(source, first_folding_challenge, second_folding_challenge, index);
  const E f1 = gkr_get_base_after_two_value(source, first_folding_challenge, second_folding_challenge, source.next_layer_size + index);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_get_continuing_points(const gkr_ext_continuing_source<E> &source, const E folding_challenge, const unsigned index, E &f0,
                                                  E &f1_or_delta) {
  f0 = gkr_get_continuing_value(source, folding_challenge, index);
  const E f1 = gkr_get_continuing_value(source, folding_challenge, source.next_layer_size + index);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E> DEVICE_FORCEINLINE void gkr_accumulate_contribution(E *dst, const unsigned index, const unsigned acc_size, const E c0, const E c1) {
  const E prev0 = load<E, ld_modifier::cs>(dst, index);
  const E prev1 = load<E, ld_modifier::cs>(dst, acc_size + index);
  store<E, st_modifier::cs>(dst, E::add(prev0, c0), index);
  store<E, st_modifier::cs>(dst, E::add(prev1, c1), acc_size + index);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_round0_values(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                                   const unsigned gid, E &c0, E &c1) {
  const E batch_challenge = batch_challenges[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  const E output_value = gkr_get_initial_value(outputs[0], gid);
  const E delta_even = gkr_get_initial_delta(inputs[0], even_index);
  const E delta_odd = gkr_get_initial_delta(inputs[0], odd_index);

  c0 = E::mul(batch_challenge, output_value);
  c1 = E::mul(batch_challenge, E::mul(delta_even, delta_odd));
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_round0_values(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                                 const unsigned gid, E &c0, E &c1) {
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  const E output_num = gkr_get_initial_value(outputs[0], gid);
  const E output_den = gkr_get_initial_value(outputs[1], gid);

  const E a = gkr_get_initial_delta(inputs[0], even_index);
  const E b = gkr_get_initial_delta(inputs[1], even_index);
  const E c = gkr_get_initial_delta(inputs[0], odd_index);
  const E d = gkr_get_initial_delta(inputs[1], odd_index);

  const E num = E::add(E::mul(a, d), E::mul(c, b));
  const E den = E::mul(b, d);

  c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
  c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_pairwise_continuation_values(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                         const unsigned gid, E &c0, E &c1) {
  const E current_folding_challenge = folding_challenge[0];
  const E batch_challenge = batch_challenges[0];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E even_f0;
  E even_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, even_index, even_f0, even_f1_or_delta);

  E odd_f0;
  E odd_f1_or_delta;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, odd_index, odd_f0, odd_f1_or_delta);

  c0 = E::mul(batch_challenge, E::mul(even_f0, odd_f0));
  c1 = E::mul(batch_challenge, E::mul(even_f1_or_delta, odd_f1_or_delta));
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_lookup_continuation_values(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                       const unsigned gid, E &out0, E &out1) {
  const E current_folding_challenge = folding_challenge[0];
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];

  const unsigned even_index = gid * 2;
  const unsigned odd_index = even_index + 1;

  E a0;
  E a1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, even_index, a0, a1);
  E b0;
  E b1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], current_folding_challenge, even_index, b0, b1);
  E c0;
  E c1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[0], current_folding_challenge, odd_index, c0, c1);
  E d0;
  E d1;
  gkr_get_continuing_points<E, EXPLICIT_FORM>(inputs[1], current_folding_challenge, odd_index, d0, d1);

  const E num0 = E::add(E::mul(a0, d0), E::mul(c0, b0));
  const E den0 = E::mul(b0, d0);
  const E num1 = E::add(E::mul(a1, d1), E::mul(c1, b1));
  const E den1 = E::mul(b1, d1);

  out0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
  out1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
}

template <typename E>
DEVICE_FORCEINLINE void gkr_pairwise_round0(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                            E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E c0;
  E c1;
  gkr_pairwise_round0_values(inputs, outputs, batch_challenges, gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_lookup_round0(const gkr_ext_initial_source<E> *inputs, const gkr_ext_initial_source<E> *outputs, const E *batch_challenges,
                                          E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E c0;
  E c1;
  gkr_lookup_round0_values(inputs, outputs, batch_challenges, gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_pairwise_continuation(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                  E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E c0;
  E c1;
  gkr_pairwise_continuation_values<E, EXPLICIT_FORM>(inputs, folding_challenge, batch_challenges, gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_lookup_continuation(const gkr_ext_continuing_source<E> *inputs, const E *folding_challenge, const E *batch_challenges,
                                                E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  E out0;
  E out1;
  gkr_lookup_continuation_values<E, EXPLICIT_FORM>(inputs, folding_challenge, batch_challenges, gid, out0, out1);
  gkr_accumulate_contribution(contributions, gid, acc_size, out0, out1);
}

DEVICE_FORCEINLINE unsigned gkr_eq_group_count(const unsigned challenge_count) {
  return challenge_count == 0 ? 0 : (challenge_count + GKR_EQ_GROUP_SIZE - 1) / GKR_EQ_GROUP_SIZE;
}

DEVICE_FORCEINLINE unsigned gkr_eq_group_size(const unsigned challenge_count, const unsigned group_idx) {
  const unsigned group_start = group_idx * GKR_EQ_GROUP_SIZE;
  if (group_start >= challenge_count)
    return 0;
  const unsigned remaining = challenge_count - group_start;
  return remaining < GKR_EQ_GROUP_SIZE ? remaining : GKR_EQ_GROUP_SIZE;
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_group_tables_from_pairs(const E *eq_pair_values, const unsigned challenge_count, E *eq_group_tables) {
  const unsigned group_idx = blockIdx.x;
  const unsigned group_size = gkr_eq_group_size(challenge_count, group_idx);
  if (group_size == 0)
    return;

  const unsigned tid = threadIdx.x;
  const unsigned chunk_count = (group_size + GKR_EQ_CHUNK_SIZE - 1) / GKR_EQ_CHUNK_SIZE;
  const unsigned group_start = group_idx * GKR_EQ_GROUP_SIZE;
  __shared__ E chunk_tables[GKR_EQ_MAX_CHUNKS_PER_GROUP][GKR_EQ_CHUNK_TABLE_LEN];

  if (tid < chunk_count * GKR_EQ_CHUNK_TABLE_LEN) {
    const unsigned chunk_idx = tid / GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned chunk_table_idx = tid % GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned variable_offset = chunk_idx * GKR_EQ_CHUNK_SIZE;
    const unsigned remaining = group_size - variable_offset;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    const unsigned chunk_len = 1u << chunk_size;
    if (chunk_table_idx < chunk_len) {
      const unsigned variable_idx = group_start + variable_offset;
      const unsigned first_bit = chunk_size == 2 ? ((chunk_table_idx >> 1) & 1u) : (chunk_table_idx & 1u);
      E value = load<E, ld_modifier::cs>(eq_pair_values, 2 * variable_idx + first_bit);
      if (chunk_size == 2) {
        const unsigned low_bit = chunk_table_idx & 1u;
        value = E::mul(value, load<E, ld_modifier::cs>(eq_pair_values, 2 * (variable_idx + 1) + low_bit));
      }
      chunk_tables[chunk_idx][chunk_table_idx] = value;
    }
  }
  __syncthreads();

  const unsigned group_len = 1u << group_size;
  if (tid >= group_len)
    return;

  E acc = E::ONE();
  unsigned consumed_bits = 0;
  for (unsigned chunk_idx = 0; chunk_idx < chunk_count; ++chunk_idx) {
    const unsigned remaining = group_size - consumed_bits;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    const unsigned shift = group_size - consumed_bits - chunk_size;
    const unsigned chunk_table_idx = (tid >> shift) & ((1u << chunk_size) - 1u);
    acc = E::mul(acc, chunk_tables[chunk_idx][chunk_table_idx]);
    consumed_bits += chunk_size;
  }

  store<E, st_modifier::cs>(eq_group_tables + group_idx * GKR_EQ_GROUP_TABLE_LEN, acc, tid);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_group_tables_from_point(const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count,
                                                             E *eq_group_tables) {
  const unsigned group_idx = blockIdx.x;
  const unsigned group_size = gkr_eq_group_size(challenge_count, group_idx);
  if (group_size == 0)
    return;

  const unsigned tid = threadIdx.x;
  const unsigned chunk_count = (group_size + GKR_EQ_CHUNK_SIZE - 1) / GKR_EQ_CHUNK_SIZE;
  const unsigned group_start = group_idx * GKR_EQ_GROUP_SIZE;
  __shared__ E chunk_tables[GKR_EQ_MAX_CHUNKS_PER_GROUP][GKR_EQ_CHUNK_TABLE_LEN];

  if (tid < chunk_count * GKR_EQ_CHUNK_TABLE_LEN) {
    const unsigned chunk_idx = tid / GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned chunk_table_idx = tid % GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned variable_offset = chunk_idx * GKR_EQ_CHUNK_SIZE;
    const unsigned remaining = group_size - variable_offset;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    const unsigned chunk_len = 1u << chunk_size;
    if (chunk_table_idx < chunk_len) {
      const unsigned variable_idx = group_start + variable_offset;
      const unsigned first_bit = chunk_size == 2 ? ((chunk_table_idx >> 1) & 1u) : (chunk_table_idx & 1u);
      const E first_challenge = load<E, ld_modifier::cs>(claim_point, challenge_offset + variable_idx);
      E value = first_bit ? first_challenge : E::sub(E::ONE(), first_challenge);
      if (chunk_size == 2) {
        const unsigned low_bit = chunk_table_idx & 1u;
        const E second_challenge = load<E, ld_modifier::cs>(claim_point, challenge_offset + variable_idx + 1);
        const E second_term = low_bit ? second_challenge : E::sub(E::ONE(), second_challenge);
        value = E::mul(value, second_term);
      }
      chunk_tables[chunk_idx][chunk_table_idx] = value;
    }
  }
  __syncthreads();

  const unsigned group_len = 1u << group_size;
  if (tid >= group_len)
    return;

  E acc = E::ONE();
  unsigned consumed_bits = 0;
  for (unsigned chunk_idx = 0; chunk_idx < chunk_count; ++chunk_idx) {
    const unsigned remaining = group_size - consumed_bits;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    const unsigned shift = group_size - consumed_bits - chunk_size;
    const unsigned chunk_table_idx = (tid >> shift) & ((1u << chunk_size) - 1u);
    acc = E::mul(acc, chunk_tables[chunk_idx][chunk_table_idx]);
    consumed_bits += chunk_size;
  }

  store<E, st_modifier::cs>(eq_group_tables + group_idx * GKR_EQ_GROUP_TABLE_LEN, acc, tid);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_values_from_group_tables(const E *eq_group_tables, const unsigned challenge_count, E *eq_values, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;
  if (challenge_count == 0) {
    store<E, st_modifier::cs>(eq_values, E::ONE(), gid);
    return;
  }

  E acc = E::ONE();
  const unsigned groups_count = gkr_eq_group_count(challenge_count);
  unsigned consumed_bits = 0;
  for (unsigned group_idx = 0; group_idx < groups_count; ++group_idx) {
    const unsigned group_size = gkr_eq_group_size(challenge_count, group_idx);
    const unsigned shift = challenge_count - consumed_bits - group_size;
    const unsigned local_gid = (gid >> shift) & ((1u << group_size) - 1u);
    acc = E::mul(acc, load<E, ld_modifier::cs>(eq_group_tables + group_idx * GKR_EQ_GROUP_TABLE_LEN, local_gid));
    consumed_bits += group_size;
  }

  store<E, st_modifier::cs>(eq_values, acc, gid);
}

template <typename E> DEVICE_FORCEINLINE void gkr_fold_eq_values_in_place(E *eq_values, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const E low = load<E, ld_modifier::cs>(eq_values, gid);
  const E high = load<E, ld_modifier::cs>(eq_values, gid + half_len);
  store<E, st_modifier::cs>(eq_values, E::add(low, high), gid);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_trace_holder_partials_shfl_xor_words(const E value, const int lane_mask, const unsigned mask, const unsigned width) {
  E result;
  constexpr unsigned words_count = sizeof(E) / sizeof(unsigned);
  const unsigned *src = reinterpret_cast<const unsigned *>(&value);
  unsigned *dst = reinterpret_cast<unsigned *>(&result);
#pragma unroll
  for (unsigned i = 0; i < words_count; ++i)
    dst[i] = shfl_xor(mask, src[i], lane_mask, width);
  return result;
}

template <typename E> DEVICE_FORCEINLINE E gkr_trace_holder_partials_shfl_xor(const E value, const int lane_mask, const unsigned mask = UINT32_MAX) {
  if constexpr (sizeof(E) % sizeof(uint4) == 0) {
    E result;
    constexpr unsigned words_count = sizeof(E) / sizeof(uint4);
    const uint4 *src = reinterpret_cast<const uint4 *>(&value);
    uint4 *dst = reinterpret_cast<uint4 *>(&result);
#pragma unroll
    for (unsigned i = 0; i < words_count; ++i)
      dst[i] = shfl_xor(mask, src[i], lane_mask, GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE);
    return result;
  } else if constexpr (sizeof(E) % sizeof(uint2) == 0) {
    E result;
    constexpr unsigned words_count = sizeof(E) / sizeof(uint2);
    const uint2 *src = reinterpret_cast<const uint2 *>(&value);
    uint2 *dst = reinterpret_cast<uint2 *>(&result);
#pragma unroll
    for (unsigned i = 0; i < words_count; ++i)
      dst[i] = shfl_xor(mask, src[i], lane_mask, GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE);
    return result;
  } else {
    return gkr_trace_holder_partials_shfl_xor_words(value, lane_mask, mask, GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE);
  }
}

template <typename E> DEVICE_FORCEINLINE E gkr_trace_holder_partials_warp_reduce_sum(E value) {
#pragma unroll
  for (int lane_mask = GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE >> 1; lane_mask > 0; lane_mask >>= 1)
    value = E::add(value, gkr_trace_holder_partials_shfl_xor(value, lane_mask));
  return value;
}

struct __align__(16) gkr_trace_holder_bf4 { bf values[4]; };

template <typename E>
DEVICE_FORCEINLINE void gkr_trace_holder_block_partials(const bf *raw_values, const E *eq_values, E *block_partials, const unsigned trace_len,
                                                        const unsigned column_start, const unsigned chunk_cols, const unsigned blocks_count) {
  static_assert(GKR_TRACE_HOLDER_PARTIALS_THREADS_PER_BLOCK % GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE == 0);
  static_assert(sizeof(gkr_trace_holder_bf4) == 4 * sizeof(bf));

  const unsigned tid = threadIdx.x;
  const unsigned lane_id = tid & (GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE - 1);
  const unsigned warp_id = tid / GKR_TRACE_HOLDER_PARTIALS_WARP_SIZE;
  const unsigned packed_trace_len = trace_len >> 2;
  const unsigned packed_gid = blockIdx.x * blockDim.x + tid;
  const unsigned packed_stride = gridDim.x * blockDim.x;
  E accumulators[GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK] = {
      E::ZERO(),
      E::ZERO(),
      E::ZERO(),
      E::ZERO(),
  };

  for (unsigned packed_row = packed_gid; packed_row < packed_trace_len; packed_row += packed_stride) {
    const unsigned row = packed_row << 2;
    const E eq0 = load<E, ld_modifier::cs>(eq_values, row);
    const E eq1 = load<E, ld_modifier::cs>(eq_values, row + 1);
    const E eq2 = load<E, ld_modifier::cs>(eq_values, row + 2);
    const E eq3 = load<E, ld_modifier::cs>(eq_values, row + 3);
#pragma unroll
    for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
      if (local_col >= chunk_cols)
        break;
      const unsigned column = column_start + local_col;
      const size_t row_offset = static_cast<size_t>(column) * trace_len + row;
      const auto values = load<gkr_trace_holder_bf4, ld_modifier::cs>(reinterpret_cast<const gkr_trace_holder_bf4 *>(raw_values), row_offset >> 2);
      E partial = E::mul(values.values[0], eq0);
      partial = E::add(partial, E::mul(values.values[1], eq1));
      partial = E::add(partial, E::mul(values.values[2], eq2));
      partial = E::add(partial, E::mul(values.values[3], eq3));
      accumulators[local_col] = E::add(accumulators[local_col], partial);
    }
  }

  __shared__ E warp_partials[GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK][GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK];
#pragma unroll
  for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
    if (local_col >= chunk_cols)
      break;
    const E warp_sum = gkr_trace_holder_partials_warp_reduce_sum(accumulators[local_col]);
    if (lane_id == 0)
      warp_partials[local_col][warp_id] = warp_sum;
  }
  __syncthreads();

  if (warp_id != 0)
    return;

#pragma unroll
  for (unsigned local_col = 0; local_col < GKR_TRACE_HOLDER_PARTIALS_COLUMNS_PER_CHUNK; ++local_col) {
    if (local_col >= chunk_cols)
      break;
    E block_sum = lane_id < GKR_TRACE_HOLDER_PARTIALS_WARPS_PER_BLOCK ? warp_partials[local_col][lane_id] : E::ZERO();
    block_sum = gkr_trace_holder_partials_warp_reduce_sum(block_sum);
    if (lane_id == 0) {
      const size_t partial_offset = static_cast<size_t>(column_start + local_col) * blocks_count + blockIdx.x;
      store<E, st_modifier::cs>(block_partials, block_sum, partial_offset);
    }
  }
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_product(const E a, const E b, E &value) { value = E::mul(a, b); }

template <typename E, typename Mask, typename Value> DEVICE_FORCEINLINE void gkr_eval_mask_identity(const Mask mask, const Value value, E &result) {
  result = E::sub(value, E::ONE());
  result = E::mul(result, mask);
  result = E::add(result, E::ONE());
}

template <typename E, typename Mask, typename Value> DEVICE_FORCEINLINE void gkr_eval_mask_identity_quadratic(const Mask mask, const Value value, E &result) {
  result = E::mul(value, mask);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_pair(const E a, const E b, const E c, const E d, E &num, E &den) {
  num = E::add(E::mul(a, d), E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E, typename B, typename D> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair(const B b, const D d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::add(shifted_b, shifted_d);
  den = E::mul(shifted_b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_ext_pair(const E b, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::add(shifted_b, shifted_d);
  den = E::mul(shifted_b, shifted_d);
}

template <typename E, typename B, typename D> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair_quadratic(const B b, const D d, E &num, E &den) {
  num = E::ZERO();
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair_quadratic(const bf b, const bf d, E &num, E &den) {
  num = E::ZERO();
  den = E::add(E::ZERO(), bf::mul(b, d));
}

template <typename E, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity(const B b, const C c, const D d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::sub(shifted_d, E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity_quadratic(const B b, const C c, const D d, E &num, E &den) {
  num = E::neg(E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity_quadratic(const bf b, const bf c, const bf d, E &num, E &den) {
  num = E::sub(E::ZERO(), bf::mul(c, b));
  den = E::add(E::ZERO(), bf::mul(b, d));
}

template <typename E, typename D, typename A, typename B>
DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced(const D d, const A a, const B b, const E gamma, E &num, E &den) {
  const E shifted_d = E::add(d, gamma);
  num = E::add(E::mul(a, shifted_d), b);
  den = E::mul(b, shifted_d);
}

template <typename E, typename D, typename A, typename B>
DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced_quadratic(const D d, const A a, const B b, E &num, E &den) {
  num = E::mul(d, a);
  den = E::mul(d, b);
}

template <typename E, typename A, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup(const A a, const B b, const C c, const D d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::sub(E::mul(a, shifted_d), E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E, typename A, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup_quadratic(const A a, const B b, const C c, const D d, E &num, E &den) {
  num = E::sub(E::mul(a, d), E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_forward_layer(const gkr_forward_layer_batch<E> &batch, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  for (unsigned gate_idx = 0; gate_idx < batch.gate_count; ++gate_idx) {
    const auto descriptor = batch.descriptors[gate_idx];
    switch (descriptor.kind) {
    case GKR_FORWARD_NO_OP:
      break;
    case GKR_FORWARD_PRODUCT: {
      const auto params = descriptor.payload.product;
      const E lhs = load<E, ld_modifier::cs>(params.lhs, gid);
      const E rhs = load<E, ld_modifier::cs>(params.rhs, gid);
      E value;
      gkr_eval_product(lhs, rhs, value);
      store<E, st_modifier::cs>(params.dst, value, gid);
      break;
    }
    case GKR_FORWARD_MASK_IDENTITY: {
      const auto params = descriptor.payload.mask_identity;
      const E input = load<E, ld_modifier::cs>(params.input, gid);
      const bf mask = load<bf, ld_modifier::cs>(params.mask, gid);
      E value;
      gkr_eval_mask_identity(mask, input, value);
      store<E, st_modifier::cs>(params.dst, value, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_PAIR: {
      const auto params = descriptor.payload.lookup_pair;
      const E a = load<E, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E c = load<E, ld_modifier::cs>(params.c, gid);
      const E d = load<E, ld_modifier::cs>(params.d, gid);
      E num;
      E den;
      gkr_eval_lookup_pair(a, b, c, d, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
      const auto params = descriptor.payload.lookup_with_cached_dens_and_setup;
      const bf a = load<bf, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const bf c = load<bf, ld_modifier::cs>(params.c, gid);
      const E d = load<E, ld_modifier::cs>(params.d, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_cached_dens_and_setup(a, b, c, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_BASE_PAIR: {
      const auto params = descriptor.payload.lookup_base_pair;
      const bf b = load<bf, ld_modifier::cs>(params.lhs, gid);
      const bf d = load<bf, ld_modifier::cs>(params.rhs, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_pair(b, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_EXT_PAIR: {
      const auto params = descriptor.payload.lookup_ext_pair;
      const E b = load<E, ld_modifier::cs>(params.lhs, gid);
      const E d = load<E, ld_modifier::cs>(params.rhs, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_ext_pair(b, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE: {
      const auto params = descriptor.payload.lookup_base_minus_multiplicity_by_base;
      const bf b = load<bf, ld_modifier::cs>(params.b, gid);
      const bf c = load<bf, ld_modifier::cs>(params.c, gid);
      const bf d = gkr_get_forward_lookup_base_setup_value(params, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_minus_multiplicity(b, c, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT: {
      const auto params = descriptor.payload.lookup_ext_minus_multiplicity_by_ext;
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const bf c = load<bf, ld_modifier::cs>(params.c, gid);
      const E d = load<E, ld_modifier::cs>(params.d, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_minus_multiplicity(b, c, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_UNBALANCED_BASE: {
      const auto params = descriptor.payload.lookup_unbalanced_base;
      const E a = load<E, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const bf d = load<bf, ld_modifier::cs>(params.remainder, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_UNBALANCED_EXTENSION: {
      const auto params = descriptor.payload.lookup_unbalanced_extension;
      const E a = load<E, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E d = load<E, ld_modifier::cs>(params.remainder, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES: {
      const auto params = descriptor.payload.initial_grand_product_without_caches;
      const E lhs = gkr_forward_memory_tuple_value(params.lhs, gid);
      const E rhs = gkr_forward_memory_tuple_value(params.rhs, gid);
      E value;
      gkr_eval_product(lhs, rhs, value);
      store<E, st_modifier::cs>(params.dst, value, gid);
      break;
    }
    case GKR_FORWARD_MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION: {
      const auto params = descriptor.payload.materialize_grand_product_term_expression;
      const E value = gkr_forward_memory_tuple_value(params.input, gid);
      store<E, st_modifier::cs>(params.dst, value, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_PAIR_FROM_BASE_INPUTS: {
      const auto params = descriptor.payload.lookup_pair_from_base_inputs;
      const bf b = bf::from_canonical_u32(params.lhs_mapping[gid]);
      const bf d = bf::from_canonical_u32(params.rhs_mapping[gid]);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_pair(b, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS: {
      const auto params = descriptor.payload.lookup_with_dens_and_setup_expressions;
      const bf enabled = load<bf, ld_modifier::cs>(params.decoder_predicate, gid);
      const bool mask = enabled.limb != 0;
      const u32 mapping = params.input_mapping[gid];
      E b = mask ? load<E, ld_modifier::cs>(params.generic_lookup, mapping) : load<E, ld_modifier::cs>(params.decoder_fill_value, 0);
      const bf a = enabled;
      const bf c = load<bf, ld_modifier::cs>(params.multiplicity, gid);
      const E d = gkr_forward_lookup_setup_value(params.generic_lookup, params.generic_lookup_len, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_cached_dens_and_setup(a, b, c, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_PAIR_FROM_VECTOR_INPUTS: {
      const auto params = descriptor.payload.lookup_pair_from_vector_inputs;
      const E b = load<E, ld_modifier::cs>(params.generic_lookup, params.lhs_mapping[gid]);
      const E d = load<E, ld_modifier::cs>(params.generic_lookup, params.rhs_mapping[gid]);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_ext_pair(b, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP: {
      const auto params = descriptor.payload.lookup_from_vector_input_with_setup;
      const E b = load<E, ld_modifier::cs>(params.generic_lookup, params.input_mapping[gid]);
      const bf c = load<bf, ld_modifier::cs>(params.multiplicity, gid);
      const E d = gkr_forward_lookup_setup_value(params.generic_lookup, params.generic_lookup_len, gid);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_minus_multiplicity(b, c, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS: {
      const auto params = descriptor.payload.lookup_unbalanced_pair_with_vector_inputs;
      const E a = load<E, ld_modifier::cs>(params.a, gid);
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E d = load<E, ld_modifier::cs>(params.generic_lookup, params.remainder_mapping[gid]);
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    default:
      return;
    }
  }
}

template <typename E> DEVICE_FORCEINLINE void gkr_dim_reducing_forward(const gkr_dim_reducing_forward_batch<E> &batch, const unsigned row_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= row_count)
    return;

  const unsigned even = gid * 2;
  const unsigned odd = even + 1;

#pragma unroll
  for (unsigned input_idx = 0; input_idx < GKR_DIM_REDUCING_FORWARD_MAX_INPUTS; ++input_idx) {
    if (input_idx >= batch.input_count)
      return;

    const auto descriptor = batch.descriptors[input_idx];
    switch (descriptor.kind) {
    case GKR_DIM_REDUCING_FORWARD_NO_OP:
      break;
    case GKR_DIM_REDUCING_FORWARD_PAIRWISE_PRODUCT: {
      const auto params = descriptor.payload.pairwise_product;
      const E lhs = load<E, ld_modifier::cs>(params.input, even);
      const E rhs = load<E, ld_modifier::cs>(params.input, odd);
      E value;
      gkr_eval_product(lhs, rhs, value);
      store<E, st_modifier::cs>(params.output, value, gid);
      break;
    }
    case GKR_DIM_REDUCING_FORWARD_LOOKUP_PAIR: {
      const auto params = descriptor.payload.lookup_pair;
      const E a = load<E, ld_modifier::cs>(params.num, even);
      const E b = load<E, ld_modifier::cs>(params.den, even);
      const E c = load<E, ld_modifier::cs>(params.num, odd);
      const E d = load<E, ld_modifier::cs>(params.den, odd);
      E num;
      E den;
      gkr_eval_lookup_pair(a, b, c, d, num, den);
      store<E, st_modifier::cs>(params.output_num, num, gid);
      store<E, st_modifier::cs>(params.output_den, den, gid);
      break;
    }
    default:
      return;
    }
  }
}

template <typename E>
DEVICE_FORCEINLINE void gkr_forward_setup_generic_lookup(const gkr_forward_setup_generic_lookup_batch<E> &batch, const unsigned row_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= row_count)
    return;

  E value = E::ZERO();

#pragma unroll
  for (unsigned column_idx = 0; column_idx < GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS; ++column_idx) {
    if (column_idx >= batch.column_count)
      break;

    const auto descriptor = batch.descriptors[column_idx];
    const bf input = load<bf, ld_modifier::cs>(descriptor.input, gid);
    const E alpha_power = load<E, ld_modifier::ca>(batch.alpha_powers, column_idx);
    value = E::add(value, E::mul(alpha_power, input));
  }

  store<E, st_modifier::cs>(batch.output, value, gid);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_eval_constraints_round0(const gkr_base_initial_source<bf> *base_inputs, const unsigned gid,
                                                 const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count) {
  E result = E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    const bf lhs = gkr_get_initial_base_delta(base_inputs[term.lhs], gid);
    const bf rhs = gkr_get_initial_base_delta(base_inputs[term.rhs], gid);
    result = E::add(result, E::mul(term.challenge, bf::mul(lhs, rhs)));
  }

  return result;
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_eval_constraints_round1(const gkr_base_after_one_source<bf, E> *base_inputs, const E first_folding_challenge, const unsigned gid,
                                                    const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count,
                                                    const gkr_main_constraint_linear_term<E> *linear_terms, const unsigned linear_terms_count,
                                                    const E constant_offset, E &eval0, E &eval1) {
  eval0 = constant_offset;
  eval1 = EXPLICIT_FORM ? constant_offset : E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs0;
    E lhs1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], first_folding_challenge, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[term.rhs], first_folding_challenge, gid, rhs0, rhs1);

    eval0 = E::add(eval0, E::mul(E::mul(lhs0, rhs0), term.challenge));
    eval1 = E::add(eval1, E::mul(E::mul(lhs1, rhs1), term.challenge));
  }
  if constexpr (EXPLICIT_FORM) {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_one_points<E, true>(base_inputs[term.input], first_folding_challenge, gid, input0, input1);
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
      eval1 = E::add(eval1, E::mul(input1, term.challenge));
    }
  } else {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_one_points<E, false>(base_inputs[term.input], first_folding_challenge, gid, input0, input1);
      (void)input1;
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
    }
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_eval_constraints_round2(const gkr_base_after_two_source<bf, E> *base_inputs, const E first_folding_challenge,
                                                    const E second_folding_challenge, const unsigned gid,
                                                    const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count,
                                                    const gkr_main_constraint_linear_term<E> *linear_terms, const unsigned linear_terms_count,
                                                    const E constant_offset, E &eval0, E &eval1) {
  eval0 = constant_offset;
  eval1 = EXPLICIT_FORM ? constant_offset : E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs0;
    E lhs1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], first_folding_challenge, second_folding_challenge, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[term.rhs], first_folding_challenge, second_folding_challenge, gid, rhs0, rhs1);

    eval0 = E::add(eval0, E::mul(E::mul(lhs0, rhs0), term.challenge));
    eval1 = E::add(eval1, E::mul(E::mul(lhs1, rhs1), term.challenge));
  }
  if constexpr (EXPLICIT_FORM) {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_two_points<E, true>(base_inputs[term.input], first_folding_challenge, second_folding_challenge, gid, input0, input1);
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
      eval1 = E::add(eval1, E::mul(input1, term.challenge));
    }
  } else {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_base_after_two_points<E, false>(base_inputs[term.input], first_folding_challenge, second_folding_challenge, gid, input0, input1);
      (void)input1;
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
    }
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_eval_constraints_round3(const gkr_ext_continuing_source<E> *base_inputs, const E folding_challenge, const unsigned gid,
                                                    const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count,
                                                    const gkr_main_constraint_linear_term<E> *linear_terms, const unsigned linear_terms_count,
                                                    const E constant_offset, E &eval0, E &eval1) {
  eval0 = constant_offset;
  eval1 = EXPLICIT_FORM ? constant_offset : E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs0;
    E lhs1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], folding_challenge, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[term.rhs], folding_challenge, gid, rhs0, rhs1);

    eval0 = E::add(eval0, E::mul(E::mul(lhs0, rhs0), term.challenge));
    eval1 = E::add(eval1, E::mul(E::mul(lhs1, rhs1), term.challenge));
  }
  if constexpr (EXPLICIT_FORM) {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_continuing_points<E, true>(base_inputs[term.input], folding_challenge, gid, input0, input1);
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
      eval1 = E::add(eval1, E::mul(input1, term.challenge));
    }
  } else {
    for (unsigned i = 0; i < linear_terms_count; ++i) {
      const auto term = linear_terms[i];
      E input0;
      E input1;
      gkr_get_continuing_points<E, false>(base_inputs[term.input], folding_challenge, gid, input0, input1);
      (void)input1;
      eval0 = E::add(eval0, E::mul(input0, term.challenge));
    }
  }
}

static constexpr u32 GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL = UINT32_MAX;

template <typename E>
DEVICE_FORCEINLINE E gkr_no_cache_linear_form_initial_value(const gkr_base_initial_source<bf> *base_inputs, const gkr_main_constraint_quadratic_term<E> *terms,
                                                            const unsigned terms_count, const unsigned gid) {
  E result = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.lhs == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      result = E::add(result, term.challenge);
    } else {
      result = E::add(result, E::mul(term.challenge, gkr_get_initial_base_value(base_inputs[term.lhs], gid)));
    }
  }
  return result;
}

template <typename E>
DEVICE_FORCEINLINE E gkr_no_cache_linear_form_initial_value(const gkr_base_initial_source<bf> *base_inputs, const gkr_main_constraint_linear_term<E> *terms,
                                                            const unsigned terms_count, const unsigned gid) {
  E result = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.input == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      result = E::add(result, term.challenge);
    } else {
      result = E::add(result, E::mul(term.challenge, gkr_get_initial_base_value(base_inputs[term.input], gid)));
    }
  }
  return result;
}

template <typename E>
DEVICE_FORCEINLINE E gkr_no_cache_linear_form_initial_delta(const gkr_base_initial_source<bf> *base_inputs, const gkr_main_constraint_quadratic_term<E> *terms,
                                                            const unsigned terms_count, const unsigned gid) {
  E result = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.lhs == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL)
      continue;
    result = E::add(result, E::mul(term.challenge, gkr_get_initial_base_delta(base_inputs[term.lhs], gid)));
  }
  return result;
}

template <typename E>
DEVICE_FORCEINLINE E gkr_no_cache_linear_form_initial_delta(const gkr_base_initial_source<bf> *base_inputs, const gkr_main_constraint_linear_term<E> *terms,
                                                            const unsigned terms_count, const unsigned gid) {
  E result = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.input == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL)
      continue;
    result = E::add(result, E::mul(term.challenge, gkr_get_initial_base_delta(base_inputs[term.input], gid)));
  }
  return result;
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_no_cache_linear_form_round1_points(const gkr_base_after_one_source<bf, E> *base_inputs, const E folding_challenge,
                                                               const gkr_main_constraint_quadratic_term<E> *terms, const unsigned terms_count,
                                                               const unsigned gid, E &eval0, E &eval1) {
  eval0 = E::ZERO();
  eval1 = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.lhs == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      eval0 = E::add(eval0, term.challenge);
      if constexpr (EXPLICIT_FORM)
        eval1 = E::add(eval1, term.challenge);
      continue;
    }
    E value0;
    E value1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], folding_challenge, gid, value0, value1);
    eval0 = E::add(eval0, E::mul(value0, term.challenge));
    eval1 = E::add(eval1, E::mul(value1, term.challenge));
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_no_cache_linear_form_round1_points(const gkr_base_after_one_source<bf, E> *base_inputs, const E folding_challenge,
                                                               const gkr_main_constraint_linear_term<E> *terms, const unsigned terms_count, const unsigned gid,
                                                               E &eval0, E &eval1) {
  eval0 = E::ZERO();
  eval1 = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.input == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      eval0 = E::add(eval0, term.challenge);
      if constexpr (EXPLICIT_FORM)
        eval1 = E::add(eval1, term.challenge);
      continue;
    }
    E value0;
    E value1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[term.input], folding_challenge, gid, value0, value1);
    eval0 = E::add(eval0, E::mul(value0, term.challenge));
    eval1 = E::add(eval1, E::mul(value1, term.challenge));
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_no_cache_linear_form_round2_points(const gkr_base_after_two_source<bf, E> *base_inputs, const E first_folding_challenge,
                                                               const E second_folding_challenge, const gkr_main_constraint_quadratic_term<E> *terms,
                                                               const unsigned terms_count, const unsigned gid, E &eval0, E &eval1) {
  eval0 = E::ZERO();
  eval1 = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.lhs == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      eval0 = E::add(eval0, term.challenge);
      if constexpr (EXPLICIT_FORM)
        eval1 = E::add(eval1, term.challenge);
      continue;
    }
    E value0;
    E value1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], first_folding_challenge, second_folding_challenge, gid, value0, value1);
    eval0 = E::add(eval0, E::mul(value0, term.challenge));
    eval1 = E::add(eval1, E::mul(value1, term.challenge));
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_no_cache_linear_form_round2_points(const gkr_base_after_two_source<bf, E> *base_inputs, const E first_folding_challenge,
                                                               const E second_folding_challenge, const gkr_main_constraint_linear_term<E> *terms,
                                                               const unsigned terms_count, const unsigned gid, E &eval0, E &eval1) {
  eval0 = E::ZERO();
  eval1 = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.input == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      eval0 = E::add(eval0, term.challenge);
      if constexpr (EXPLICIT_FORM)
        eval1 = E::add(eval1, term.challenge);
      continue;
    }
    E value0;
    E value1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[term.input], first_folding_challenge, second_folding_challenge, gid, value0, value1);
    eval0 = E::add(eval0, E::mul(value0, term.challenge));
    eval1 = E::add(eval1, E::mul(value1, term.challenge));
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_no_cache_linear_form_round3_points(const gkr_ext_continuing_source<E> *base_inputs, const E folding_challenge,
                                                               const gkr_main_constraint_quadratic_term<E> *terms, const unsigned terms_count,
                                                               const unsigned gid, E &eval0, E &eval1) {
  eval0 = E::ZERO();
  eval1 = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.lhs == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      eval0 = E::add(eval0, term.challenge);
      if constexpr (EXPLICIT_FORM)
        eval1 = E::add(eval1, term.challenge);
      continue;
    }
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[term.lhs], folding_challenge, gid, value0, value1);
    eval0 = E::add(eval0, E::mul(value0, term.challenge));
    eval1 = E::add(eval1, E::mul(value1, term.challenge));
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_no_cache_linear_form_round3_points(const gkr_ext_continuing_source<E> *base_inputs, const E folding_challenge,
                                                               const gkr_main_constraint_linear_term<E> *terms, const unsigned terms_count, const unsigned gid,
                                                               E &eval0, E &eval1) {
  eval0 = E::ZERO();
  eval1 = E::ZERO();
  for (unsigned i = 0; i < terms_count; ++i) {
    const auto term = terms[i];
    if (term.input == GKR_NO_CACHE_LINEAR_FORM_CONSTANT_SENTINEL) {
      eval0 = E::add(eval0, term.challenge);
      if constexpr (EXPLICIT_FORM)
        eval1 = E::add(eval1, term.challenge);
      continue;
    }
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[term.input], folding_challenge, gid, value0, value1);
    eval0 = E::add(eval0, E::mul(value0, term.challenge));
    eval1 = E::add(eval1, E::mul(value1, term.challenge));
  }
}

template <typename E>
DEVICE_FORCEINLINE void
gkr_main_round0_values(const unsigned kind, const gkr_base_initial_source<bf> *base_inputs, const gkr_ext_initial_source<E> *ext_inputs,
                       const gkr_base_initial_source<bf> *base_outputs, const gkr_ext_initial_source<E> *ext_outputs, const E *batch_challenges,
                       const E aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                       const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                       const unsigned constraint_linear_terms_count, const E constraint_constant_offset, const unsigned gid, E &c0, E &c1) {
  (void)aux_challenge;
  (void)constraint_linear_terms;
  (void)constraint_linear_terms_count;
  (void)constraint_constant_offset;
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];

  c0 = E::ZERO();
  c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    const bf output_value = gkr_get_initial_base_value(base_outputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    break;
  }
  case GKR_MAIN_LINEAR_BASE_OUTPUT: {
    const bf output_value = gkr_get_initial_base_value(base_outputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    break;
  }
  case GKR_MAIN_INITS_AND_TEARDOWNS_INITIAL_PAIR: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    c1 = E::mul(batch_challenge_0, gkr_eval_constraints_round0(base_inputs, gid, constraint_quadratic_terms, constraint_quadratic_terms_count));
    break;
  }
  case GKR_MAIN_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    const E lhs_delta = gkr_no_cache_linear_form_initial_delta(base_inputs, constraint_quadratic_terms, constraint_quadratic_terms_count, gid);
    const E rhs_delta = gkr_no_cache_linear_form_initial_delta(base_inputs, constraint_linear_terms, constraint_linear_terms_count, gid);
    c0 = E::mul(batch_challenge_0, output_value);
    c1 = E::mul(batch_challenge_0, E::mul(lhs_delta, rhs_delta));
    break;
  }
  case GKR_MAIN_MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    const E delta = gkr_no_cache_linear_form_initial_delta(base_inputs, constraint_linear_terms, constraint_linear_terms_count, gid);
    c0 = E::mul(batch_challenge_0, output_value);
    c1 = E::mul(batch_challenge_0, delta);
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    break;
  }
  case GKR_MAIN_PRODUCT: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    c1 = E::mul(batch_challenge_0, E::mul(delta_a, delta_b));
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    const E output_value = gkr_get_initial_value(ext_outputs[0], gid);
    const bf delta_mask = gkr_get_initial_base_delta(base_inputs[0], gid);
    const E delta_value = gkr_get_initial_delta(ext_inputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
    c1 = E::mul(batch_challenge_0, E::mul(delta_mask, delta_value));
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    const E delta_c = gkr_get_initial_delta(ext_inputs[2], gid);
    const E delta_d = gkr_get_initial_delta(ext_inputs[3], gid);
    E num;
    E den;
    gkr_eval_lookup_pair(delta_a, delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const bf delta_b = gkr_get_initial_base_delta(base_inputs[0], gid);
    const bf delta_d = gkr_get_initial_base_delta(base_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_base_pair_quadratic(delta_b, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR_FROM_BASE_INPUTS:
  case GKR_MAIN_LOOKUP_PAIR_FROM_VECTOR_INPUTS: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_b = gkr_no_cache_linear_form_initial_delta(base_inputs, constraint_quadratic_terms, constraint_quadratic_terms_count, gid);
    const E delta_d = gkr_no_cache_linear_form_initial_delta(base_inputs, constraint_linear_terms, constraint_linear_terms_count, gid);
    E num;
    E den;
    gkr_eval_lookup_base_pair_quadratic(delta_b, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_PAIR: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_d = gkr_get_initial_delta(ext_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_base_pair_quadratic(delta_b, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const bf delta_b = gkr_get_initial_base_delta(base_inputs[0], gid);
    const bf delta_c = gkr_get_initial_base_delta(base_inputs[1], gid);
    const bf delta_d = gkr_get_initial_base_delta(base_inputs[2], gid);
    E num;
    E den;
    gkr_eval_lookup_base_minus_multiplicity_quadratic(delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const bf delta_a = gkr_get_initial_base_delta(base_inputs[0], gid);
    const bf delta_c = gkr_get_initial_base_delta(base_inputs[1], gid);
    const E delta_b = gkr_no_cache_linear_form_initial_delta(base_inputs + 2, constraint_quadratic_terms, constraint_quadratic_terms_count, gid);
    const E delta_d = gkr_no_cache_linear_form_initial_delta(base_inputs + 2, constraint_linear_terms, constraint_linear_terms_count, gid);
    E num;
    E den;
    gkr_eval_lookup_cached_dens_and_setup_quadratic(delta_a, delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const bf delta_c = gkr_get_initial_base_delta(base_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_d = gkr_get_initial_delta(ext_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_base_minus_multiplicity_quadratic(delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const bf delta_c = gkr_get_initial_base_delta(base_inputs[0], gid);
    const E delta_b = gkr_no_cache_linear_form_initial_delta(base_inputs + 1, constraint_quadratic_terms, constraint_quadratic_terms_count, gid);
    const E delta_d = gkr_no_cache_linear_form_initial_delta(base_inputs + 1, constraint_linear_terms, constraint_linear_terms_count, gid);
    E num;
    E den;
    gkr_eval_lookup_base_minus_multiplicity_quadratic(delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const bf delta_d = gkr_get_initial_base_delta(base_inputs[0], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_unbalanced_quadratic(delta_d, delta_a, delta_b, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_EXTENSION: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    const E delta_d = gkr_get_initial_delta(ext_inputs[2], gid);
    E num;
    E den;
    gkr_eval_lookup_unbalanced_quadratic(delta_d, delta_a, delta_b, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
    const E delta_d = gkr_no_cache_linear_form_initial_delta(base_inputs, constraint_linear_terms, constraint_linear_terms_count, gid);
    E num;
    E den;
    gkr_eval_lookup_unbalanced_quadratic(delta_d, delta_a, delta_b, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    const E output_num = gkr_get_initial_value(ext_outputs[0], gid);
    const E output_den = gkr_get_initial_value(ext_outputs[1], gid);
    const bf delta_a = gkr_get_initial_base_delta(base_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[0], gid);
    const bf delta_c = gkr_get_initial_base_delta(base_inputs[1], gid);
    const E delta_d = gkr_get_initial_delta(ext_inputs[1], gid);
    E num;
    E den;
    gkr_eval_lookup_cached_dens_and_setup_quadratic(delta_a, delta_b, delta_c, delta_d, num, den);
    c0 = E::add(E::mul(batch_challenge_0, output_num), E::mul(batch_challenge_1, output_den));
    c1 = E::add(E::mul(batch_challenge_0, num), E::mul(batch_challenge_1, den));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    c1 = E::mul(batch_challenge_0, gkr_eval_constraints_round0(base_inputs, gid, constraint_quadratic_terms, constraint_quadratic_terms_count));
    break;
  }
  default:
    return;
  }
}

template <typename E>
DEVICE_FORCEINLINE void
gkr_main_round0(const unsigned kind, const gkr_base_initial_source<bf> *base_inputs, const gkr_ext_initial_source<E> *ext_inputs,
                const gkr_base_initial_source<bf> *base_outputs, const gkr_ext_initial_source<E> *ext_outputs, const E *batch_challenges,
                const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E c0;
  E c1;
  gkr_main_round0_values(kind, base_inputs, ext_inputs, base_outputs, ext_outputs, batch_challenges, aux_challenge ? aux_challenge[0] : E::ZERO(),
                         constraint_quadratic_terms, constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count,
                         constraint_constant_offset ? constraint_constant_offset[0] : E::ZERO(), gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round1_values(const unsigned kind, const gkr_base_after_one_source<bf, E> *base_inputs,
                                               const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges, const E *folding_challenge,
                                               const E aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                                               const unsigned constraint_quadratic_terms_count,
                                               const gkr_main_constraint_linear_term<E> *constraint_linear_terms, const unsigned constraint_linear_terms_count,
                                               const E constraint_constant_offset, const unsigned gid, E &c0, E &c1) {
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];
  const E current_folding_challenge = folding_challenge[0];
  const E current_aux_challenge = aux_challenge;

  c0 = E::ZERO();
  c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_LINEAR_BASE_OUTPUT: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round1<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, nullptr, 0, constraint_linear_terms,
                                                  constraint_linear_terms_count, constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_INITS_AND_TEARDOWNS_INITIAL_PAIR: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round1<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, constraint_quadratic_terms, constraint_quadratic_terms_count,
                                                  constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES: {
    E lhs0;
    E lhs1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, rhs0, rhs1);
    E eval0;
    E eval1;
    gkr_eval_product(lhs0, rhs0, eval0);
    gkr_eval_product(lhs1, rhs1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION: {
    E eval0;
    E eval1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_PRODUCT: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E eval0;
    E eval1;
    gkr_eval_product(a0, b0, eval0);
    gkr_eval_product(a1, b1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    E mask0;
    E mask1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, mask0, mask1);
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, value0, value1);
    E eval0;
    E eval1;
    gkr_eval_mask_identity(mask0, value0, eval0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_mask_identity(mask1, value1, eval1);
    } else {
      gkr_eval_mask_identity_quadratic(mask1, value1, eval1);
    }
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[3], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_pair(a0, b0, c0_in, d0, num0, den0);
    gkr_eval_lookup_pair(a1, b1, c1_in, d1, num1, den1);
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    E b0;
    E b1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR_FROM_BASE_INPUTS:
  case GKR_MAIN_LOOKUP_PAIR_FROM_VECTOR_INPUTS: {
    E b0;
    E b1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_PAIR: {
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    E b0;
    E b1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[2], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS: {
    E a0;
    E a1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs + 2, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs + 2, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT: {
    E c0_in;
    E c1_in;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP: {
    E c0_in;
    E c1_in;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs + 1, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs + 1, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    E d0;
    E d1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_EXTENSION: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS: {
    E d0;
    E d1;
    gkr_no_cache_linear_form_round1_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    E a0;
    E a1;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round1<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, constraint_quadratic_terms, constraint_quadratic_terms_count,
                                                  constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  default:
    return;
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round1(const unsigned kind, const gkr_base_after_one_source<bf, E> *base_inputs,
                                        const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges, const E *folding_challenge,
                                        const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                                        const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                                        const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions,
                                        const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E c0;
  E c1;
  gkr_main_round1_values<E, EXPLICIT_FORM>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge ? aux_challenge[0] : E::ZERO(),
                                           constraint_quadratic_terms, constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count,
                                           constraint_constant_offset ? constraint_constant_offset[0] : E::ZERO(), gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round2_values(const unsigned kind, const gkr_base_after_two_source<bf, E> *base_inputs,
                                               const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges, const E *folding_challenges,
                                               const E aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                                               const unsigned constraint_quadratic_terms_count,
                                               const gkr_main_constraint_linear_term<E> *constraint_linear_terms, const unsigned constraint_linear_terms_count,
                                               const E constraint_constant_offset, const unsigned gid, E &c0, E &c1) {
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];
  const E first_folding_challenge = folding_challenges[0];
  const E second_folding_challenge = folding_challenges[1];
  const E current_aux_challenge = aux_challenge;

  c0 = E::ZERO();
  c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_LINEAR_BASE_OUTPUT: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round2<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, gid, nullptr, 0, constraint_linear_terms,
                                                  constraint_linear_terms_count, constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_INITS_AND_TEARDOWNS_INITIAL_PAIR: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round2<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, gid, constraint_quadratic_terms,
                                                  constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count,
                                                  constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES: {
    E lhs0;
    E lhs1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, constraint_linear_terms,
                                                             constraint_linear_terms_count, gid, rhs0, rhs1);
    E eval0;
    E eval1;
    gkr_eval_product(lhs0, rhs0, eval0);
    gkr_eval_product(lhs1, rhs1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION: {
    E eval0;
    E eval1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, constraint_linear_terms,
                                                             constraint_linear_terms_count, gid, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_PRODUCT: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E eval0;
    E eval1;
    gkr_eval_product(a0, b0, eval0);
    gkr_eval_product(a1, b1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    E mask0;
    E mask1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, mask0, mask1);
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, value0, value1);
    E eval0;
    E eval1;
    gkr_eval_mask_identity(mask0, value0, eval0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_mask_identity(mask1, value1, eval1);
    } else {
      gkr_eval_mask_identity_quadratic(mask1, value1, eval1);
    }
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], second_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[3], second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_pair(a0, b0, c0_in, d0, num0, den0);
    gkr_eval_lookup_pair(a1, b1, c1_in, d1, num1, den1);
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    E b0;
    E b1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[1], first_folding_challenge, second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR_FROM_BASE_INPUTS:
  case GKR_MAIN_LOOKUP_PAIR_FROM_VECTOR_INPUTS: {
    E b0;
    E b1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, constraint_linear_terms,
                                                             constraint_linear_terms_count, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_PAIR: {
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    E b0;
    E b1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[1], first_folding_challenge, second_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[2], first_folding_challenge, second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS: {
    E a0;
    E a1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[1], first_folding_challenge, second_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs + 2, first_folding_challenge, second_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs + 2, first_folding_challenge, second_folding_challenge, constraint_linear_terms,
                                                             constraint_linear_terms_count, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT: {
    E c0_in;
    E c1_in;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP: {
    E c0_in;
    E c1_in;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs + 1, first_folding_challenge, second_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs + 1, first_folding_challenge, second_folding_challenge, constraint_linear_terms,
                                                             constraint_linear_terms_count, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    E d0;
    E d1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_EXTENSION: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS: {
    E d0;
    E d1;
    gkr_no_cache_linear_form_round2_points<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, constraint_linear_terms,
                                                             constraint_linear_terms_count, gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    E a0;
    E a1;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[0], first_folding_challenge, second_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(base_inputs[1], first_folding_challenge, second_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], second_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], second_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round2<E, EXPLICIT_FORM>(base_inputs, first_folding_challenge, second_folding_challenge, gid, constraint_quadratic_terms,
                                                  constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count,
                                                  constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  default:
    return;
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round2(const unsigned kind, const gkr_base_after_two_source<bf, E> *base_inputs,
                                        const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges, const E *folding_challenges,
                                        const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                                        const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                                        const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions,
                                        const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E c0;
  E c1;
  gkr_main_round2_values<E, EXPLICIT_FORM>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenges, aux_challenge ? aux_challenge[0] : E::ZERO(),
                                           constraint_quadratic_terms, constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count,
                                           constraint_constant_offset ? constraint_constant_offset[0] : E::ZERO(), gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round3_values(const unsigned kind, const gkr_ext_continuing_source<E> *base_inputs,
                                               const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges, const E *folding_challenge,
                                               const E aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                                               const unsigned constraint_quadratic_terms_count,
                                               const gkr_main_constraint_linear_term<E> *constraint_linear_terms, const unsigned constraint_linear_terms_count,
                                               const E constraint_constant_offset, const unsigned gid, E &c0, E &c1) {
  const E batch_challenge_0 = batch_challenges[0];
  const E batch_challenge_1 = batch_challenges[1];
  const E current_folding_challenge = folding_challenge[0];
  const E current_aux_challenge = aux_challenge;

  c0 = E::ZERO();
  c1 = E::ZERO();
  switch (kind) {
  case GKR_MAIN_BASE_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_LINEAR_BASE_OUTPUT: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round3<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, nullptr, 0, constraint_linear_terms,
                                                  constraint_linear_terms_count, constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_INITS_AND_TEARDOWNS_INITIAL_PAIR: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round3<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, constraint_quadratic_terms, constraint_quadratic_terms_count,
                                                  constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_INITIAL_GRAND_PRODUCT_WITHOUT_CACHES: {
    E lhs0;
    E lhs1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, lhs0, lhs1);
    E rhs0;
    E rhs1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, rhs0, rhs1);
    E eval0;
    E eval1;
    gkr_eval_product(lhs0, rhs0, eval0);
    gkr_eval_product(lhs1, rhs1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION: {
    E eval0;
    E eval1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_EXT_COPY: {
    E f0;
    E f1_or_delta;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, f0, f1_or_delta);
    c0 = E::mul(batch_challenge_0, f0);
    c1 = EXPLICIT_FORM ? E::mul(batch_challenge_0, f1_or_delta) : E::ZERO();
    break;
  }
  case GKR_MAIN_PRODUCT: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E eval0;
    E eval1;
    gkr_eval_product(a0, b0, eval0);
    gkr_eval_product(a1, b1, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_MASK_IDENTITY: {
    E mask0;
    E mask1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, mask0, mask1);
    E value0;
    E value1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, value0, value1);
    E eval0;
    E eval1;
    gkr_eval_mask_identity(mask0, value0, eval0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_mask_identity(mask1, value1, eval1);
    } else {
      gkr_eval_mask_identity_quadratic(mask1, value1, eval1);
    }
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[3], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_pair(a0, b0, c0_in, d0, num0, den0);
    gkr_eval_lookup_pair(a1, b1, c1_in, d1, num1, den1);
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_PAIR: {
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_PAIR_FROM_BASE_INPUTS:
  case GKR_MAIN_LOOKUP_PAIR_FROM_VECTOR_INPUTS: {
    E b0;
    E b1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_PAIR: {
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_pair(b0, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_pair(b1, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_pair_quadratic(b1, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_BASE_MINUS_MULTIPLICITY: {
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, b0, b1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[2], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs + 2, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs + 2, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT: {
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP: {
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs + 1, current_folding_challenge, constraint_quadratic_terms,
                                                             constraint_quadratic_terms_count, gid, b0, b1);
    E d0;
    E d1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs + 1, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_base_minus_multiplicity(b0, c0_in, d0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_base_minus_multiplicity(b1, c1_in, d1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_base_minus_multiplicity_quadratic(b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED: {
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_EXTENSION: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[2], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS: {
    E d0;
    E d1;
    gkr_no_cache_linear_form_round3_points<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, constraint_linear_terms, constraint_linear_terms_count,
                                                             gid, d0, d1);
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, a0, a1);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, b0, b1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_unbalanced(d0, a0, b0, E::ZERO(), num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_unbalanced(d1, a1, b1, E::ZERO(), num1, den1);
    } else {
      gkr_eval_lookup_unbalanced_quadratic(d1, a1, b1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP: {
    E a0;
    E a1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[0], current_folding_challenge, gid, a0, a1);
    E c0_in;
    E c1_in;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(base_inputs[1], current_folding_challenge, gid, c0_in, c1_in);
    E b0;
    E b1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[0], current_folding_challenge, gid, b0, b1);
    E d0;
    E d1;
    gkr_get_continuing_points<E, EXPLICIT_FORM>(ext_inputs[1], current_folding_challenge, gid, d0, d1);
    E num0;
    E den0;
    E num1;
    E den1;
    gkr_eval_lookup_cached_dens_and_setup(a0, b0, c0_in, d0, current_aux_challenge, num0, den0);
    if constexpr (EXPLICIT_FORM) {
      gkr_eval_lookup_cached_dens_and_setup(a1, b1, c1_in, d1, current_aux_challenge, num1, den1);
    } else {
      gkr_eval_lookup_cached_dens_and_setup_quadratic(a1, b1, c1_in, d1, num1, den1);
    }
    c0 = E::add(E::mul(batch_challenge_0, num0), E::mul(batch_challenge_1, den0));
    c1 = E::add(E::mul(batch_challenge_0, num1), E::mul(batch_challenge_1, den1));
    break;
  }
  case GKR_MAIN_ENFORCE_CONSTRAINTS: {
    E eval0;
    E eval1;
    gkr_eval_constraints_round3<E, EXPLICIT_FORM>(base_inputs, current_folding_challenge, gid, constraint_quadratic_terms, constraint_quadratic_terms_count,
                                                  constraint_linear_terms, constraint_linear_terms_count, constraint_constant_offset, eval0, eval1);
    c0 = E::mul(batch_challenge_0, eval0);
    c1 = E::mul(batch_challenge_0, eval1);
    break;
  }
  default:
    return;
  }
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void
gkr_main_round3(const unsigned kind, const gkr_ext_continuing_source<E> *base_inputs, const gkr_ext_continuing_source<E> *ext_inputs, const E *batch_challenges,
                const E *folding_challenge, const E *aux_challenge, const gkr_main_constraint_quadratic_term<E> *constraint_quadratic_terms,
                const unsigned constraint_quadratic_terms_count, const gkr_main_constraint_linear_term<E> *constraint_linear_terms,
                const unsigned constraint_linear_terms_count, const E *constraint_constant_offset, E *contributions, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E c0;
  E c1;
  gkr_main_round3_values<E, EXPLICIT_FORM>(kind, base_inputs, ext_inputs, batch_challenges, folding_challenge, aux_challenge ? aux_challenge[0] : E::ZERO(),
                                           constraint_quadratic_terms, constraint_quadratic_terms_count, constraint_linear_terms, constraint_linear_terms_count,
                                           constraint_constant_offset ? constraint_constant_offset[0] : E::ZERO(), gid, c0, c1);
  gkr_accumulate_contribution(contributions, gid, acc_size, c0, c1);
}

template <typename E> DEVICE_FORCEINLINE void gkr_dim_reducing_round0_batched(const gkr_dim_reducing_round0_batch<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    const bool descriptors_inline = gkr_dim_reducing_batch_descriptors_inline(record.record_mode);
    const auto *inputs = gkr_main_batch_payload_ptr<gkr_ext_initial_source<E>>(batch, record.extension_inputs, descriptors_inline);
    const auto *outputs = gkr_main_batch_payload_ptr<gkr_ext_initial_source<E>>(batch, record.extension_outputs, descriptors_inline);
    E batch_challenge_storage[2];
    const E *batch_challenges =
        gkr_main_batch_challenges(batch.batch_challenge_base, record.batch_challenge_offset, record.batch_challenge_count, batch_challenge_storage);
    E c0;
    E c1;
    switch (record.kind) {
    case GKR_DIM_REDUCING_PAIRWISE:
      gkr_pairwise_round0_values(inputs, outputs, batch_challenges, gid, c0, c1);
      break;
    case GKR_DIM_REDUCING_LOOKUP:
      gkr_lookup_round0_values(inputs, outputs, batch_challenges, gid, c0, c1);
      break;
    default:
      return;
    }
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = load<E, ld_modifier::cs>(batch.eq_values, gid);
  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM, typename Batch>
DEVICE_FORCEINLINE void gkr_dim_reducing_continuation_batched(const Batch &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    const bool descriptors_inline = gkr_dim_reducing_batch_descriptors_inline(record.record_mode);
    const auto *inputs = gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch, record.extension_inputs, descriptors_inline);
    E batch_challenge_storage[2];
    const E *batch_challenges =
        gkr_main_batch_challenges(batch.batch_challenge_base, record.batch_challenge_offset, record.batch_challenge_count, batch_challenge_storage);
    E c0;
    E c1;
    switch (record.kind) {
    case GKR_DIM_REDUCING_PAIRWISE:
      gkr_pairwise_continuation_values<E, EXPLICIT_FORM>(inputs, batch.folding_challenge, batch_challenges, gid, c0, c1);
      break;
    case GKR_DIM_REDUCING_LOOKUP:
      gkr_lookup_continuation_values<E, EXPLICIT_FORM>(inputs, batch.folding_challenge, batch_challenges, gid, c0, c1);
      break;
    default:
      return;
    }
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = load<E, ld_modifier::cs>(batch.eq_values, gid);
  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E>
DEVICE_FORCEINLINE void gkr_main_round0_batched(const gkr_main_round0_batch_static<E> &batch_static, const gkr_main_round0_batch_runtime<E> &batch_runtime,
                                                const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  unsigned consumed_batch_challenges = 0;
  for (unsigned i = 0; i < batch_static.record_count; ++i) {
    const auto &record = batch_static.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs =
        gkr_main_batch_payload_ptr<gkr_base_initial_source<bf>>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);
    const auto *extension_inputs =
        gkr_main_batch_payload_ptr<gkr_ext_initial_source<E>>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);
    const auto *base_outputs =
        gkr_main_batch_payload_ptr<gkr_base_initial_source<bf>>(batch_static, batch_runtime.spill_payload, record.base_outputs, descriptors_inline);
    const auto *extension_outputs =
        gkr_main_batch_payload_ptr<gkr_ext_initial_source<E>>(batch_static, batch_runtime.spill_payload, record.extension_outputs, descriptors_inline);
    const E *batch_challenges = batch_runtime.batch_challenges + consumed_batch_challenges;
    const E auxiliary_challenge = batch_runtime.auxiliary_challenges == nullptr ? record.auxiliary_challenge : batch_runtime.auxiliary_challenges[i];
    consumed_batch_challenges += gkr_main_kind_batch_challenge_count(record.kind);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch_static, batch_runtime.spill_payload, record,
                                       batch_runtime.constraint_metadata == nullptr ? nullptr : &batch_runtime.constraint_metadata[i], quadratic_terms,
                                       quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round0_values(record.kind, base_inputs, extension_inputs, base_outputs, extension_outputs, batch_challenges, auxiliary_challenge, quadratic_terms,
                           quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = load<E, ld_modifier::cs>(batch_runtime.eq_values, gid);
  store<E, st_modifier::cs>(batch_runtime.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch_runtime.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round1_batched(const gkr_main_round1_batch_static<E> &batch_static, const gkr_main_round1_batch_runtime<E> &batch_runtime,
                                                const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  unsigned consumed_batch_challenges = 0;
  for (unsigned i = 0; i < batch_static.record_count; ++i) {
    const auto &record = batch_static.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs =
        gkr_main_batch_payload_ptr<gkr_base_after_one_source<bf, E>>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);
    const auto *extension_inputs =
        gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);
    const E *batch_challenges = batch_runtime.batch_challenges + consumed_batch_challenges;
    const E auxiliary_challenge = batch_runtime.auxiliary_challenges == nullptr ? record.auxiliary_challenge : batch_runtime.auxiliary_challenges[i];
    consumed_batch_challenges += gkr_main_kind_batch_challenge_count(record.kind);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch_static, batch_runtime.spill_payload, record,
                                       batch_runtime.constraint_metadata == nullptr ? nullptr : &batch_runtime.constraint_metadata[i], quadratic_terms,
                                       quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round1_values<E, EXPLICIT_FORM>(record.kind, base_inputs, extension_inputs, batch_challenges, batch_runtime.folding_challenge, auxiliary_challenge,
                                             quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = load<E, ld_modifier::cs>(batch_runtime.eq_values, gid);
  store<E, st_modifier::cs>(batch_runtime.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch_runtime.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round2_batched(const gkr_main_round2_batch_static<E> &batch_static, const gkr_main_round2_batch_runtime<E> &batch_runtime,
                                                const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  unsigned consumed_batch_challenges = 0;
  for (unsigned i = 0; i < batch_static.record_count; ++i) {
    const auto &record = batch_static.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs =
        gkr_main_batch_payload_ptr<gkr_base_after_two_source<bf, E>>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);
    const auto *extension_inputs =
        gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);
    const E *batch_challenges = batch_runtime.batch_challenges + consumed_batch_challenges;
    const E auxiliary_challenge = batch_runtime.auxiliary_challenges == nullptr ? record.auxiliary_challenge : batch_runtime.auxiliary_challenges[i];
    consumed_batch_challenges += gkr_main_kind_batch_challenge_count(record.kind);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch_static, batch_runtime.spill_payload, record,
                                       batch_runtime.constraint_metadata == nullptr ? nullptr : &batch_runtime.constraint_metadata[i], quadratic_terms,
                                       quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round2_values<E, EXPLICIT_FORM>(record.kind, base_inputs, extension_inputs, batch_challenges, batch_runtime.folding_challenges,
                                             auxiliary_challenge, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset,
                                             gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = load<E, ld_modifier::cs>(batch_runtime.eq_values, gid);
  store<E, st_modifier::cs>(batch_runtime.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch_runtime.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void gkr_main_round3_batched(const gkr_main_round3_batch_static<E> &batch_static, const gkr_main_round3_batch_runtime<E> &batch_runtime,
                                                const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E total0 = E::ZERO();
  E total1 = E::ZERO();
  unsigned consumed_batch_challenges = 0;
  for (unsigned i = 0; i < batch_static.record_count; ++i) {
    const auto &record = batch_static.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs =
        gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch_static, batch_runtime.spill_payload, record.base_inputs, descriptors_inline);
    const auto *extension_inputs =
        gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch_static, batch_runtime.spill_payload, record.extension_inputs, descriptors_inline);
    const E *batch_challenges = batch_runtime.batch_challenges + consumed_batch_challenges;
    const E auxiliary_challenge = batch_runtime.auxiliary_challenges == nullptr ? record.auxiliary_challenge : batch_runtime.auxiliary_challenges[i];
    consumed_batch_challenges += gkr_main_kind_batch_challenge_count(record.kind);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch_static, batch_runtime.spill_payload, record,
                                       batch_runtime.constraint_metadata == nullptr ? nullptr : &batch_runtime.constraint_metadata[i], quadratic_terms,
                                       quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round3_values<E, EXPLICIT_FORM>(record.kind, base_inputs, extension_inputs, batch_challenges, batch_runtime.folding_challenge, auxiliary_challenge,
                                             quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  const E eq = load<E, ld_modifier::cs>(batch_runtime.eq_values, gid);
  store<E, st_modifier::cs>(batch_runtime.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch_runtime.contributions + acc_size, E::mul(total1, eq), gid);
}

} // namespace airbender::prover::gkr
