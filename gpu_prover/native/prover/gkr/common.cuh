#pragma once

#include "../../common.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::prover::gkr {

template <typename E> struct gkr_ext_initial_source {
  const E *start;
  size_t next_layer_size;
};

template <typename B> struct gkr_base_initial_source {
  const B *start;
  size_t next_layer_size;
};

template <typename B, typename E> struct gkr_base_after_one_source {
  size_t base_layer_half_size;
  size_t next_layer_size;
  const B *base_input_start;
};

template <typename B, typename E> struct gkr_base_after_two_source {
  const B *base_input_start;
  E *this_layer_cache_start;
  size_t base_layer_half_size;
  size_t base_quarter_size;
  size_t next_layer_size;
  bool first_access;
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
  GKR_MAIN_LOOKUP_UNBALANCED = 7,
  GKR_MAIN_LOOKUP_WITH_CACHED_DENS_AND_SETUP = 8,
  GKR_MAIN_ENFORCE_CONSTRAINTS = 9,
};

static constexpr unsigned GKR_FORWARD_MAX_GATES_PER_LAYER = 64;
static constexpr unsigned GKR_BACKWARD_MAX_KERNELS_PER_LAYER = 64;
static constexpr unsigned GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES = 12 * 1024;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_MAX_INPUTS = 5;
static constexpr unsigned GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS = 10;

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
  E constant_offset;
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
  u32 batch_challenge_offset;
  u32 batch_challenge_count;
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
  u32 batch_challenge_offset;
  u32 batch_challenge_count;
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
  u32 batch_challenge_offset;
  u32 batch_challenge_count;
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
  u32 batch_challenge_offset;
  u32 batch_challenge_count;
  gkr_main_payload_range quadratic_terms;
  gkr_main_payload_range linear_terms;
  E auxiliary_challenge;
  E constant_offset;
};

template <typename E> struct gkr_main_round0_batch {
  u32 record_count;
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
  const E *batch_challenge_base;
  E *contributions;
  const u8 *spill_payload;
  gkr_main_round0_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_main_round1_batch {
  u32 record_count;
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
  const E *batch_challenge_base;
  const E *folding_challenge;
  E *contributions;
  const u8 *spill_payload;
  bool explicit_form;
  u8 padding[7];
  gkr_main_round1_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_main_round2_batch {
  u32 record_count;
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
  const E *batch_challenge_base;
  const E *folding_challenges;
  E *contributions;
  const u8 *spill_payload;
  bool explicit_form;
  u8 padding[7];
  gkr_main_round2_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_main_round3_batch {
  u32 record_count;
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
  const E *batch_challenge_base;
  const E *folding_challenge;
  E *contributions;
  const u8 *spill_payload;
  bool explicit_form;
  u8 padding[7];
  gkr_main_round3_batch_record<E> records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

DEVICE_FORCEINLINE bool gkr_main_batch_descriptors_inline(const u32 record_mode) { return record_mode != GKR_MAIN_BATCH_POINTER_DESCRIPTORS; }

template <typename T, typename Batch>
DEVICE_FORCEINLINE const T *gkr_main_batch_payload_ptr(const Batch &batch, const gkr_main_payload_range &range, const bool from_inline) {
  if (range.count == 0)
    return nullptr;
  const u8 *base = from_inline ? batch.inline_payload : batch.spill_payload;
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

template <typename E, typename Batch, typename Record>
DEVICE_FORCEINLINE void gkr_main_batch_constraint_metadata(const Batch &batch, const Record &record,
                                                           const gkr_main_constraint_quadratic_term<E> *&quadratic_terms, unsigned &quadratic_terms_count,
                                                           const gkr_main_constraint_linear_term<E> *&linear_terms, unsigned &linear_terms_count,
                                                           E &constant_offset) {
  const bool metadata_inline = record.metadata_inline != 0;
  quadratic_terms = gkr_main_batch_payload_ptr<gkr_main_constraint_quadratic_term<E>>(batch, record.quadratic_terms, metadata_inline);
  quadratic_terms_count = record.quadratic_terms.count;
  linear_terms = gkr_main_batch_payload_ptr<gkr_main_constraint_linear_term<E>>(batch, record.linear_terms, metadata_inline);
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
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
  const E *batch_challenge_base;
  E *contributions;
  const u8 *spill_payload;
  gkr_dim_reducing_round0_batch_record records[GKR_BACKWARD_MAX_KERNELS_PER_LAYER];
  u8 inline_payload[GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES];
};

template <typename E> struct gkr_dim_reducing_round1_batch {
  u32 record_count;
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
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
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
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
  u32 challenge_offset;
  u32 challenge_count;
  u32 reserved;
  const E *claim_point;
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

enum gkr_forward_gate_kind : u32 {
  GKR_FORWARD_NO_OP = 0,
  GKR_FORWARD_PRODUCT = 1,
  GKR_FORWARD_MASK_IDENTITY = 2,
  GKR_FORWARD_LOOKUP_PAIR = 3,
  GKR_FORWARD_LOOKUP_WITH_CACHED_DENS_AND_SETUP = 4,
  GKR_FORWARD_LOOKUP_BASE_PAIR = 5,
  GKR_FORWARD_LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE = 6,
  GKR_FORWARD_LOOKUP_UNBALANCED_BASE = 7,
  GKR_FORWARD_LOOKUP_UNBALANCED_EXTENSION = 8,
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

template <typename E> struct gkr_forward_lookup_base_minus_multiplicity_by_base_descriptor {
  const bf *b;
  const bf *c;
  const bf *d;
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

template <typename E> union gkr_forward_gate_payload {
  gkr_forward_no_op_descriptor no_op;
  gkr_forward_product_descriptor<E> product;
  gkr_forward_mask_identity_descriptor<E> mask_identity;
  gkr_forward_lookup_pair_descriptor<E> lookup_pair;
  gkr_forward_lookup_with_cached_dens_and_setup_descriptor<E> lookup_with_cached_dens_and_setup;
  gkr_forward_lookup_base_pair_descriptor<E> lookup_base_pair;
  gkr_forward_lookup_base_minus_multiplicity_by_base_descriptor<E> lookup_base_minus_multiplicity_by_base;
  gkr_forward_lookup_unbalanced_base_descriptor<E> lookup_unbalanced_base;
  gkr_forward_lookup_unbalanced_extension_descriptor<E> lookup_unbalanced_extension;
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
constexpr unsigned GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS = 6;

enum gkr_forward_cache_kind : u32 {
  GKR_FORWARD_CACHE_EMPTY = 0,
  GKR_FORWARD_CACHE_SINGLE_COLUMN_LOOKUP = 1,
  GKR_FORWARD_CACHE_VECTORIZED_LOOKUP = 2,
  GKR_FORWARD_CACHE_VECTORIZED_LOOKUP_SETUP = 3,
  GKR_FORWARD_CACHE_MEMORY_TUPLE = 4,
};

enum gkr_forward_cache_address_space_kind : u32 {
  GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY = 0,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT = 1,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_IS = 2,
  GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT = 3,
};

template <typename E> struct gkr_forward_cache_descriptor {
  gkr_forward_cache_kind kind;
  gkr_forward_cache_address_space_kind address_space_kind;
  const u32 *mapping;
  const bf *setup_values;
  const E *generic_lookup;
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

template <typename E> DEVICE_FORCEINLINE E gkr_lift_base(const bf value) { return E::mul(E::ONE(), value); }

template <typename E> DEVICE_FORCEINLINE void gkr_forward_cache_memory_tuple(const gkr_forward_cache_descriptor<E> &descriptor, const unsigned gid) {
  E value = descriptor.constant_term;
  switch (descriptor.address_space_kind) {
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT:
    value = E::add(value, gkr_lift_base<E>(descriptor.address_space_constant));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_IS:
    value = E::add(value, gkr_lift_base<E>(load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid)));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT:
    value = E::add(value, E::sub(E::ONE(), gkr_lift_base<E>(load<bf, ld_modifier::cs>(descriptor.address_space_ptr, gid))));
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
      const bf value = load<bf, ld_modifier::cs>(descriptor.setup_values, mapping);
      store<bf, st_modifier::cs>(descriptor.base_output, value, gid);
      break;
    }
    case GKR_FORWARD_CACHE_VECTORIZED_LOOKUP: {
      const unsigned mapping = descriptor.mapping[gid];
      const E value = load<E, ld_modifier::cs>(descriptor.generic_lookup, mapping);
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

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_base_value(const gkr_base_initial_source<bf> &source, const unsigned index) {
  return gkr_lift_base<E>(load<bf, ld_modifier::cs>(source.start, index));
}

template <typename E> DEVICE_FORCEINLINE E gkr_get_initial_base_delta(const gkr_base_initial_source<bf> &source, const unsigned index) {
  const bf f0 = load<bf, ld_modifier::cs>(source.start, index);
  const bf f1 = load<bf, ld_modifier::cs>(source.start, source.next_layer_size + index);
  return gkr_lift_base<E>(bf::sub(f1, f0));
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
  const bf f0 = load<bf, ld_modifier::cs>(source.base_input_start, index);
  const bf f1 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_layer_half_size + index);
  const bf diff = bf::sub(f1, f0);
  return E::add(E::mul(first_folding_challenge, diff), f0);
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

  const bf f00 = load<bf, ld_modifier::cs>(source.base_input_start, index);
  const bf f01 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_layer_half_size + index);
  const bf f10 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_quarter_size + index);
  const bf f11 = load<bf, ld_modifier::cs>(source.base_input_start, source.base_layer_half_size + source.base_quarter_size + index);

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

template <typename E>
DEVICE_FORCEINLINE void gkr_build_eq_values(const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count, E *eq_values,
                                            const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  E acc = E::ONE();
  for (unsigned i = 0; i < challenge_count; ++i) {
    const E challenge = load<E, ld_modifier::cs>(claim_point, challenge_offset + i);
    const bool bit = ((gid >> (challenge_count - 1 - i)) & 1u) != 0;
    const E term = bit ? challenge : E::sub(E::ONE(), challenge);
    acc = E::mul(acc, term);
  }

  store<E, st_modifier::cs>(eq_values, acc, gid);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_eq_weight_at(const E *claim_point, const unsigned challenge_offset, const unsigned challenge_count, const unsigned gid) {
  E acc = E::ONE();
  for (unsigned i = 0; i < challenge_count; ++i) {
    const E challenge = load<E, ld_modifier::cs>(claim_point, challenge_offset + i);
    const bool bit = ((gid >> (challenge_count - 1 - i)) & 1u) != 0;
    const E term = bit ? challenge : E::sub(E::ONE(), challenge);
    acc = E::mul(acc, term);
  }
  return acc;
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_product(const E a, const E b, E &value) { value = E::mul(a, b); }

template <typename E> DEVICE_FORCEINLINE void gkr_eval_mask_identity(const E mask, const E value, E &result) {
  result = E::sub(value, E::ONE());
  result = E::mul(result, mask);
  result = E::add(result, E::ONE());
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_mask_identity_quadratic(const E mask, const E value, E &result) { result = E::mul(value, mask); }

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_pair(const E a, const E b, const E c, const E d, E &num, E &den) {
  num = E::add(E::mul(a, d), E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair(const E b, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::add(shifted_b, shifted_d);
  den = E::mul(shifted_b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_pair_quadratic(const E b, const E d, E &num, E &den) {
  num = E::ZERO();
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity(const E b, const E c, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::sub(shifted_d, E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_base_minus_multiplicity_quadratic(const E b, const E c, const E d, E &num, E &den) {
  (void)d;
  num = E::neg(E::mul(c, b));
  den = E::mul(b, d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced(const E d, const E a, const E b, const E gamma, E &num, E &den) {
  const E shifted_d = E::add(d, gamma);
  num = E::add(E::mul(a, shifted_d), b);
  den = E::mul(b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced_quadratic(const E d, const E a, const E b, E &num, E &den) {
  num = E::mul(d, a);
  den = E::mul(d, b);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup(const E a, const E b, const E c, const E d, const E gamma, E &num, E &den) {
  const E shifted_b = E::add(b, gamma);
  const E shifted_d = E::add(d, gamma);
  num = E::sub(E::mul(a, shifted_d), E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E> DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup_quadratic(const E a, const E b, const E c, const E d, E &num, E &den) {
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
      const E mask = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.mask, gid));
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
      const E a = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.a, gid));
      const E b = load<E, ld_modifier::cs>(params.b, gid);
      const E c = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.c, gid));
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
      const E b = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.lhs, gid));
      const E d = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.rhs, gid));
      const E gamma = load<E, ld_modifier::cs>(batch.lookup_additive_challenge, 0);
      E num;
      E den;
      gkr_eval_lookup_base_pair(b, d, gamma, num, den);
      store<E, st_modifier::cs>(params.num, num, gid);
      store<E, st_modifier::cs>(params.den, den, gid);
      break;
    }
    case GKR_FORWARD_LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE: {
      const auto params = descriptor.payload.lookup_base_minus_multiplicity_by_base;
      const E b = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.b, gid));
      const E c = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.c, gid));
      const E d = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.d, gid));
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
      const E d = gkr_lift_base<E>(load<bf, ld_modifier::cs>(params.remainder, gid));
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
    value = E::add(value, E::mul(gkr_lift_base<E>(input), alpha_power));
  }

  store<E, st_modifier::cs>(batch.output, value, gid);
}

template <typename E>
DEVICE_FORCEINLINE E gkr_eval_constraints_round0(const gkr_base_initial_source<bf> *base_inputs, const unsigned gid,
                                                 const gkr_main_constraint_quadratic_term<E> *quadratic_terms, const unsigned quadratic_terms_count) {
  E result = E::ZERO();
  for (unsigned i = 0; i < quadratic_terms_count; ++i) {
    const auto term = quadratic_terms[i];
    E lhs = gkr_get_initial_base_delta<E>(base_inputs[term.lhs], gid);
    const E rhs = gkr_get_initial_base_delta<E>(base_inputs[term.rhs], gid);
    lhs = E::mul(lhs, rhs);
    lhs = E::mul(lhs, term.challenge);
    result = E::add(result, lhs);
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
    const E output_value = gkr_get_initial_base_value<E>(base_outputs[0], gid);
    c0 = E::mul(batch_challenge_0, output_value);
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
    const E delta_mask = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
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
    const E delta_b = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_d = gkr_get_initial_base_delta<E>(base_inputs[1], gid);
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
    const E delta_b = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_c = gkr_get_initial_base_delta<E>(base_inputs[1], gid);
    const E delta_d = gkr_get_initial_base_delta<E>(base_inputs[2], gid);
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
    const E delta_d = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_a = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[1], gid);
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
    const E delta_a = gkr_get_initial_base_delta<E>(base_inputs[0], gid);
    const E delta_b = gkr_get_initial_delta(ext_inputs[0], gid);
    const E delta_c = gkr_get_initial_base_delta<E>(base_inputs[1], gid);
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

  const E eq = gkr_eq_weight_at(batch.claim_point, batch.challenge_offset, batch.challenge_count, gid);
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

  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM, typename Batch>
DEVICE_FORCEINLINE void gkr_dim_reducing_continuation_batched(const Batch &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const E eq = gkr_eq_weight_at(batch.claim_point, batch.challenge_offset, batch.challenge_count, gid);
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

  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E> DEVICE_FORCEINLINE void gkr_main_round0_batched(const gkr_main_round0_batch<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const E eq = gkr_eq_weight_at(batch.claim_point, batch.challenge_offset, batch.challenge_count, gid);
  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs = gkr_main_batch_payload_ptr<gkr_base_initial_source<bf>>(batch, record.base_inputs, descriptors_inline);
    const auto *extension_inputs = gkr_main_batch_payload_ptr<gkr_ext_initial_source<E>>(batch, record.extension_inputs, descriptors_inline);
    const auto *base_outputs = gkr_main_batch_payload_ptr<gkr_base_initial_source<bf>>(batch, record.base_outputs, descriptors_inline);
    const auto *extension_outputs = gkr_main_batch_payload_ptr<gkr_ext_initial_source<E>>(batch, record.extension_outputs, descriptors_inline);
    E batch_challenge_storage[2];
    const E *batch_challenges =
        gkr_main_batch_challenges(batch.batch_challenge_base, record.batch_challenge_offset, record.batch_challenge_count, batch_challenge_storage);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch, record, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round0_values(record.kind, base_inputs, extension_inputs, base_outputs, extension_outputs, batch_challenges, record.auxiliary_challenge,
                           quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM> DEVICE_FORCEINLINE void gkr_main_round1_batched(const gkr_main_round1_batch<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const E eq = gkr_eq_weight_at(batch.claim_point, batch.challenge_offset, batch.challenge_count, gid);
  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs = gkr_main_batch_payload_ptr<gkr_base_after_one_source<bf, E>>(batch, record.base_inputs, descriptors_inline);
    const auto *extension_inputs = gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch, record.extension_inputs, descriptors_inline);
    E batch_challenge_storage[2];
    const E *batch_challenges =
        gkr_main_batch_challenges(batch.batch_challenge_base, record.batch_challenge_offset, record.batch_challenge_count, batch_challenge_storage);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch, record, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round1_values<E, EXPLICIT_FORM>(record.kind, base_inputs, extension_inputs, batch_challenges, batch.folding_challenge, record.auxiliary_challenge,
                                             quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM> DEVICE_FORCEINLINE void gkr_main_round2_batched(const gkr_main_round2_batch<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const E eq = gkr_eq_weight_at(batch.claim_point, batch.challenge_offset, batch.challenge_count, gid);
  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs = gkr_main_batch_payload_ptr<gkr_base_after_two_source<bf, E>>(batch, record.base_inputs, descriptors_inline);
    const auto *extension_inputs = gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch, record.extension_inputs, descriptors_inline);
    E batch_challenge_storage[2];
    const E *batch_challenges =
        gkr_main_batch_challenges(batch.batch_challenge_base, record.batch_challenge_offset, record.batch_challenge_count, batch_challenge_storage);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch, record, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round2_values<E, EXPLICIT_FORM>(record.kind, base_inputs, extension_inputs, batch_challenges, batch.folding_challenges, record.auxiliary_challenge,
                                             quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

template <typename E, bool EXPLICIT_FORM> DEVICE_FORCEINLINE void gkr_main_round3_batched(const gkr_main_round3_batch<E> &batch, const unsigned acc_size) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= acc_size)
    return;

  const E eq = gkr_eq_weight_at(batch.claim_point, batch.challenge_offset, batch.challenge_count, gid);
  E total0 = E::ZERO();
  E total1 = E::ZERO();
  for (unsigned i = 0; i < batch.record_count; ++i) {
    const auto &record = batch.records[i];
    const bool descriptors_inline = gkr_main_batch_descriptors_inline(record.record_mode);
    const auto *base_inputs = gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch, record.base_inputs, descriptors_inline);
    const auto *extension_inputs = gkr_main_batch_payload_ptr<gkr_ext_continuing_source<E>>(batch, record.extension_inputs, descriptors_inline);
    E batch_challenge_storage[2];
    const E *batch_challenges =
        gkr_main_batch_challenges(batch.batch_challenge_base, record.batch_challenge_offset, record.batch_challenge_count, batch_challenge_storage);
    const gkr_main_constraint_quadratic_term<E> *quadratic_terms;
    const gkr_main_constraint_linear_term<E> *linear_terms;
    unsigned quadratic_terms_count;
    unsigned linear_terms_count;
    E constant_offset;
    gkr_main_batch_constraint_metadata(batch, record, quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset);
    E c0;
    E c1;
    gkr_main_round3_values<E, EXPLICIT_FORM>(record.kind, base_inputs, extension_inputs, batch_challenges, batch.folding_challenge, record.auxiliary_challenge,
                                             quadratic_terms, quadratic_terms_count, linear_terms, linear_terms_count, constant_offset, gid, c0, c1);
    total0 = E::add(total0, c0);
    total1 = E::add(total1, c1);
  }

  store<E, st_modifier::cs>(batch.contributions, E::mul(total0, eq), gid);
  store<E, st_modifier::cs>(batch.contributions + acc_size, E::mul(total1, eq), gid);
}

} // namespace airbender::prover::gkr
