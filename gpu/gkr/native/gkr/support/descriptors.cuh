#pragma once

#include "common.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::gkr {

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

template <typename E> struct gkr_ext_continuing_source {
  const E *previous_layer_start;
  E *this_layer_start;
  size_t this_layer_size;
  size_t next_layer_size;
  bool first_access;
};

// Dim-reducing layers are keyed by OutputType: 2 pairwise records for
// PermutationProduct, up to 3 lookup records, plus (unified circuit)
// 2 pairwise records for InitsAndTeardownsProduct = 7 records / 10 challenges.
// Kept in lockstep with the Rust mirror by `compact_cuda_constants_match_rust`.
static constexpr unsigned GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER = 7;
static constexpr unsigned GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN = 10;
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
// Number of warp-uniform high slabs in the strict 3-slot eq layout.
// Fixed for the lifetime of a layer; high slabs degrade in place
// (slot 0 holds identity 1) once their g_size reaches 0.
static constexpr unsigned GKR_EQ_HIGH_SLOTS = 2;

// Sizes for the strict 3-slot eq layout. Mirrors
// `ab_gkr_eq_high[GKR_EQ_HIGH_SLOTS][...]` for the high pair plus a single
// low slot held in global memory.
struct gkr_eq_sizes {
  unsigned high[GKR_EQ_HIGH_SLOTS];
  unsigned low;
};

static_assert(alignof(gkr_eq_sizes) == 4 && sizeof(gkr_eq_sizes) == 12, "eq sizes ABI drift");
static_assert(__builtin_offsetof(gkr_eq_sizes, high) == 0 && __builtin_offsetof(gkr_eq_sizes, low) == 8, "eq sizes offsets drift");

enum gkr_dim_reducing_kernel_kind : u32 {
  GKR_DIM_REDUCING_PAIRWISE = 0,
  GKR_DIM_REDUCING_LOOKUP = 1,
};

constexpr unsigned GKR_DIM_REDUCING_INLINE_RECORD_CAP = 28;
// The 4-bit pointer index in each source encoding addresses this table.
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
  u16 reserved;
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
  const E *eq_low;
  gkr_eq_sizes eq_sizes;
  u32 eq_sizes_pad;
  E *contributions;
  gkr_dim_reducing_tables tables;
  gkr_dim_reducing_batch_record_compact records[GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER];
  gkr_source_record inline_payload[GKR_DIM_REDUCING_INLINE_RECORD_CAP];
};

template <typename E> struct gkr_dim_reducing_continuation_batch_compact {
  u32 record_count;
  u32 reserved0;
  const E *eq_low;
  gkr_eq_sizes eq_sizes;
  u32 eq_sizes_pad;
  E *contributions;
  gkr_dim_reducing_tables tables;
  gkr_dim_reducing_batch_record_compact records[GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER];
  gkr_source_record inline_payload[GKR_DIM_REDUCING_INLINE_RECORD_CAP];
};

static_assert(sizeof(gkr_dim_reducing_round0_batch_compact<e4>) == 456, "round-0 descriptor ABI drift");
static_assert(sizeof(gkr_dim_reducing_continuation_batch_compact<e4>) == 456, "continuation descriptor ABI drift");
static_assert(alignof(gkr_dim_reducing_payload_range_16) == 2 && sizeof(gkr_dim_reducing_payload_range_16) == 4, "payload range ABI drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_payload_range_16, offset) == 0 && __builtin_offsetof(gkr_dim_reducing_payload_range_16, count) == 2,
              "payload range offsets drift");
static_assert(alignof(gkr_dim_reducing_batch_record_compact) == 4 && sizeof(gkr_dim_reducing_batch_record_compact) == 16, "batch record ABI drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_batch_record_compact, kind) == 0 && __builtin_offsetof(gkr_dim_reducing_batch_record_compact, inputs) == 4 &&
                  __builtin_offsetof(gkr_dim_reducing_batch_record_compact, outputs) == 8 &&
                  __builtin_offsetof(gkr_dim_reducing_batch_record_compact, batch_challenge_offset) == 12 &&
                  __builtin_offsetof(gkr_dim_reducing_batch_record_compact, reserved) == 14,
              "batch record offsets drift");
static_assert(alignof(gkr_dim_reducing_tables) == 8 && sizeof(gkr_dim_reducing_tables) == 192, "dim-reducing tables ABI drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_tables, bases) == 0 && __builtin_offsetof(gkr_dim_reducing_tables, log2_stride) == 128,
              "dim-reducing table offsets drift");
static_assert(alignof(gkr_source_record) == 2 && sizeof(gkr_source_record) == 4, "source record ABI drift");
static_assert(__builtin_offsetof(gkr_source_record, src) == 0 && __builtin_offsetof(gkr_source_record, cache) == 2, "source record offsets drift");
static_assert(alignof(gkr_dim_reducing_round0_batch_compact<e4>) == 8, "round-0 descriptor alignment drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, record_count) == 0 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, reserved0) == 4 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, eq_low) == 8 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, eq_sizes) == 16 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, eq_sizes_pad) == 28 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, contributions) == 32 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, tables) == 40 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, records) == 232 &&
                  __builtin_offsetof(gkr_dim_reducing_round0_batch_compact<e4>, inline_payload) == 344,
              "round-0 descriptor offsets drift");
static_assert(sizeof(gkr_dim_reducing_round0_batch_compact<e4>) + sizeof(u32) <= 32764, "round-0 kernel parameters exceed CUDA limit");
static_assert(alignof(gkr_dim_reducing_continuation_batch_compact<e4>) == 8, "continuation descriptor alignment drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, record_count) == 0 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, reserved0) == 4 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, eq_low) == 8 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, eq_sizes) == 16 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, eq_sizes_pad) == 28 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, contributions) == 32 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, tables) == 40 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, records) == 232 &&
                  __builtin_offsetof(gkr_dim_reducing_continuation_batch_compact<e4>, inline_payload) == 344,
              "continuation descriptor offsets drift");
static_assert(sizeof(gkr_dim_reducing_continuation_batch_compact<e4>) + 2 * sizeof(u32) <= 32764, "continuation kernel parameters exceed CUDA limit");

// Merged tower batch (blockIdx.y selects the pair). A pair's two streams are either two
// independent product towers (PAIRWISE2) or one lookup tower's num/den (LOOKUP).
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_PAIR_CAP = 5;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_PAIRWISE2 = 0;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_LOOKUP = 1;

template <typename E> struct gkr_dim_reducing_forward_tower_pair {
  const E *input[2];
  E *round_outputs[GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS][2];
  u32 kind;
  u32 reserved;
};

template <typename E> struct gkr_dim_reducing_forward_tower_batch {
  gkr_dim_reducing_forward_tower_pair<E> pairs[GKR_DIM_REDUCING_FORWARD_TOWER_PAIR_CAP];
  u32 pair_count;
  u32 input_len;
  u32 round_count;
  u32 reserved;
};

static_assert(sizeof(gkr_dim_reducing_forward_tower_pair<e4>) == 152, "tower pair ABI size drift");
static_assert(sizeof(gkr_dim_reducing_forward_tower_batch<e4>) == 776, "tower batch ABI size drift");
static_assert(alignof(gkr_dim_reducing_forward_tower_batch<e4>) == 8, "tower batch ABI alignment drift");

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

static constexpr unsigned GKR_TIMESTAMP_COLUMNS_NUM_BITS = 19;

// Maximum inputs / outputs read by a dim-reducing kernel-kind. Pairwise uses (1 input, 1 output);
// Lookup uses (2 inputs, 2 outputs). Sized to the lookup case so the stack array never overflows.
constexpr unsigned GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD = 2;
constexpr unsigned GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD = 2;

} // namespace airbender::gkr

// __constant__ batch-challenge table for dim-reducing backward compact kernels.
// Defined in backward/dim_reducing.cu.
EXTERN __device__ __constant__ e4 ab_gkr_dim_reducing_batch_challenge_table[airbender::gkr::GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_dim_reducing_layer_claim_point[airbender::gkr::GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_lookup_alpha_powers[airbender::gkr::GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
