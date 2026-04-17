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

static constexpr unsigned GKR_BACKWARD_MAX_KERNELS_PER_LAYER = 64;
static constexpr unsigned GKR_BACKWARD_MAX_INLINE_ROUND_BATCH_BYTES = 12 * 1024;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK = 8;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK = 1u << GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS = GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
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

struct gkr_main_payload_range {
  u32 offset;
  u32 count;
};

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

// Tower batches: one per slot (no cross-slot batching). Each tower kernel consumes a single slot's
// contiguous input row range (B = GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK elements per block) and
// drives it down `round_count` halving levels through shared memory, writing each intermediate
// level to DRAM for the backward pass.
template <typename E> struct gkr_dim_reducing_forward_tower_pairwise_batch {
  const E *input;
  E *round_outputs[GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS];
  u32 input_len;
  u32 round_count;
};

template <typename E> struct gkr_dim_reducing_forward_tower_lookup_batch {
  const E *input_num;
  const E *input_den;
  E *round_outputs_num[GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS];
  E *round_outputs_den[GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS];
  u32 input_len;
  u32 round_count;
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
    value = E::fma(descriptor.linear_challenges[term], input, value);
  }

  store<E, st_modifier::cs>(descriptor.ext_output, value, gid);
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
  const E folded = E::fma(folding_challenge, diff, f0);
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
  const E folded = E::fma(first_folding_challenge, diff, f0);
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
  result = E::fma(second_folding_challenge, c10, result);
  result = E::fma(combined_challenges, c11, result);
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

  const E num = E::fma(a, d, E::mul(c, b));
  const E den = E::mul(b, d);

  c0 = E::fma(batch_challenge_0, output_num, E::mul(batch_challenge_1, output_den));
  c1 = E::fma(batch_challenge_0, num, E::mul(batch_challenge_1, den));
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

  const E num0 = E::fma(a0, d0, E::mul(c0, b0));
  const E den0 = E::mul(b0, d0);
  const E num1 = E::fma(a1, d1, E::mul(c1, b1));
  const E den1 = E::mul(b1, d1);

  out0 = E::fma(batch_challenge_0, num0, E::mul(batch_challenge_1, den0));
  out1 = E::fma(batch_challenge_0, num1, E::mul(batch_challenge_1, den1));
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
      partial = E::fma(eq1, values.values[1], partial);
      partial = E::fma(eq2, values.values[2], partial);
      partial = E::fma(eq3, values.values[3], partial);
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
  num = E::fma(a, d, E::mul(c, b));
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
  den = E::from_scalar(bf::mul(b, d));
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
  num = E::neg(E::from_scalar(bf::mul(c, b)));
  den = E::from_scalar(bf::mul(b, d));
}

template <typename E, typename D, typename A, typename B>
DEVICE_FORCEINLINE void gkr_eval_lookup_unbalanced(const D d, const A a, const B b, const E gamma, E &num, E &den) {
  const E shifted_d = E::add(d, gamma);
  num = E::fma(a, shifted_d, b);
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
  num = E::fms(a, shifted_d, E::mul(c, shifted_b));
  den = E::mul(shifted_b, shifted_d);
}

template <typename E, typename A, typename B, typename C, typename D>
DEVICE_FORCEINLINE void gkr_eval_lookup_cached_dens_and_setup_quadratic(const A a, const B b, const C c, const D d, E &num, E &den) {
  num = E::fms(a, d, E::mul(c, b));
  den = E::mul(b, d);
}

// Pairwise-product tower: each block consumes B = blockDim.x contiguous input rows (or fewer, in
// the single-block tail) and fuses up to log2(B) halving rounds in shared memory. Every round's
// output is also written to DRAM for backward consumption.
template <typename E>
DEVICE_FORCEINLINE void gkr_dim_reducing_forward_tower_pairwise(const gkr_dim_reducing_forward_tower_pairwise_batch<E> &batch) {
  extern __shared__ E smem_pairwise[];

  const unsigned tid = threadIdx.x;
  const unsigned bid = blockIdx.x;
  const unsigned base = bid * blockDim.x;

  // Round-0 load from DRAM to shmem. Threads outside the valid tail range idle.
  if (base + tid < batch.input_len)
    smem_pairwise[tid] = load<E, ld_modifier::cs>(batch.input, base + tid);
  __syncthreads();

  // For body launches, cur_len == blockDim.x == B. For the single-block tail where
  // input_len < B, only the first input_len threads carried real data.
  unsigned cur_len = blockDim.x < batch.input_len ? blockDim.x : batch.input_len;
  for (unsigned r = 0; r < batch.round_count; ++r) {
    cur_len >>= 1;
    E out;
    const bool active = tid < cur_len;
    if (active) {
      const E lhs = smem_pairwise[2 * tid];
      const E rhs = smem_pairwise[2 * tid + 1];
      gkr_eval_product(lhs, rhs, out);
      // Coalesced DRAM write — block b's slice of this level is [b*cur_len, (b+1)*cur_len).
      store<E, st_modifier::cs>(batch.round_outputs[r], out, bid * cur_len + tid);
    }
    __syncthreads();  // Read phase complete; safe to overwrite shmem.
    if (active)
      smem_pairwise[tid] = out;
    __syncthreads();  // Next round may read a wider slice; ensure all writes visible.
  }
}

// Lookup-pair tower: same shape as pairwise but with num/den shmem buffers side by side.
template <typename E>
DEVICE_FORCEINLINE void gkr_dim_reducing_forward_tower_lookup(const gkr_dim_reducing_forward_tower_lookup_batch<E> &batch) {
  extern __shared__ E smem_lookup[];
  E *smem_num = smem_lookup;
  E *smem_den = smem_lookup + blockDim.x;

  const unsigned tid = threadIdx.x;
  const unsigned bid = blockIdx.x;
  const unsigned base = bid * blockDim.x;

  if (base + tid < batch.input_len) {
    smem_num[tid] = load<E, ld_modifier::cs>(batch.input_num, base + tid);
    smem_den[tid] = load<E, ld_modifier::cs>(batch.input_den, base + tid);
  }
  __syncthreads();

  unsigned cur_len = blockDim.x < batch.input_len ? blockDim.x : batch.input_len;
  for (unsigned r = 0; r < batch.round_count; ++r) {
    cur_len >>= 1;
    E out_num;
    E out_den;
    const bool active = tid < cur_len;
    if (active) {
      const E a = smem_num[2 * tid];
      const E b = smem_den[2 * tid];
      const E c = smem_num[2 * tid + 1];
      const E d = smem_den[2 * tid + 1];
      gkr_eval_lookup_pair(a, b, c, d, out_num, out_den);
      store<E, st_modifier::cs>(batch.round_outputs_num[r], out_num, bid * cur_len + tid);
      store<E, st_modifier::cs>(batch.round_outputs_den[r], out_den, bid * cur_len + tid);
    }
    __syncthreads();
    if (active) {
      smem_num[tid] = out_num;
      smem_den[tid] = out_den;
    }
    __syncthreads();
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
    value = E::fma(alpha_power, input, value);
  }

  store<E, st_modifier::cs>(batch.output, value, gid);
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

} // namespace airbender::prover::gkr
