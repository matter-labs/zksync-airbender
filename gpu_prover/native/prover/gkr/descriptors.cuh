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

template <typename E> struct gkr_ext_continuing_source {
  const E *previous_layer_start;
  E *this_layer_start;
  size_t this_layer_size;
  size_t next_layer_size;
  bool first_access;
};

static constexpr unsigned GKR_BACKWARD_MAX_KERNELS_PER_LAYER = 128;
// Dim-reducing layers are keyed by OutputType: 2 pairwise records for
// PermutationProduct plus up to 3 lookup records, consuming 8 challenges.
static constexpr unsigned GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER = 5;
static constexpr unsigned GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN = 8;
static constexpr unsigned GKR_BACKWARD_MAX_TRACE_LEN_LOG2 = 24;
// Dim-reducing stores folding_steps - 1 round challenges plus 3 transcript challenges.
static constexpr unsigned GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 2;
// Main layers store folding_steps - 1 round challenges plus 2 transcript challenges.
static constexpr unsigned GKR_MAIN_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 1;
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

enum gkr_dim_reducing_kernel_kind : u32 {
  GKR_DIM_REDUCING_PAIRWISE = 0,
  GKR_DIM_REDUCING_LOOKUP = 1,
};

constexpr unsigned GKR_DIM_REDUCING_INLINE_U16_BUDGET = 1280;
// 4-bit ptr_idx in every u16 source encoding sizes the backing pool: each main-layer
// flat launch needs one slot per backing (read + cache for both base and ext), so the
// table holds up to 16 entries.
constexpr unsigned GKR_DIM_REDUCING_BASE_SLOTS = 16;

struct gkr_dim_reducing_payload_range_16 {
  u16 offset;
  u16 count;
};

struct gkr_dim_reducing_batch_record_compact {
  u32 kind;
  gkr_dim_reducing_payload_range_16 inputs;
  gkr_dim_reducing_payload_range_16 outputs;
  u16 batch_challenge_offset;
  u16 batch_challenge_count;
};

static_assert(sizeof(gkr_dim_reducing_batch_record_compact) == 16, "compact batch record must be 16 B");

struct gkr_dim_reducing_tables {
  const u8 *bases[GKR_DIM_REDUCING_BASE_SLOTS];
  u32 log2_stride[GKR_DIM_REDUCING_BASE_SLOTS];
};

struct gkr_source_record {
  u16 src;
  u16 cache;
};

template <typename E> struct gkr_dim_reducing_round0_batch_compact {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  const E *eq_values;
  E *contributions;
  gkr_dim_reducing_tables tables;
  gkr_dim_reducing_batch_record_compact records[GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER];
  gkr_source_record inline_payload[GKR_DIM_REDUCING_INLINE_U16_BUDGET];
};

template <typename E> struct gkr_dim_reducing_continuation_batch_compact {
  u32 record_count;
  u32 reserved0;
  u32 reserved1;
  u32 reserved2;
  const E *eq_values;
  E *contributions;
  bool explicit_form;
  u8 padding[7];
  gkr_dim_reducing_tables tables;
  gkr_dim_reducing_batch_record_compact records[GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER];
  gkr_source_record inline_payload[GKR_DIM_REDUCING_INLINE_U16_BUDGET];
};

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
  u32 decoder_table_id;
  E *output;
  E *decoder_fill_value_out;
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

// Maximum inputs / outputs read by a dim-reducing kernel-kind. Pairwise uses (1 input, 1 output);
// Lookup uses (2 inputs, 2 outputs). Sized to the lookup case so the stack array never overflows.
constexpr unsigned GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD = 2;
constexpr unsigned GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD = 2;

} // namespace airbender::prover::gkr

// __constant__ batch-challenge table for dim-reducing backward compact kernels.
// Defined in dim_reducing_backward.cu.
EXTERN __device__ __constant__ e4 ab_gkr_dim_reducing_batch_challenge_table[airbender::prover::gkr::GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_dim_reducing_layer_claim_point[airbender::prover::gkr::GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_lookup_alpha_powers[airbender::prover::gkr::GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
