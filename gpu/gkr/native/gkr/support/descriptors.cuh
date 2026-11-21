#pragma once

#include "common.cuh"
#include "primitives/memory.cuh"

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

// Input poly index is `2*Y + b`, gate bit `b` lowest; the sumcheck binds `Y` LSB-first, so row `j` spans GKR_DIM_REDUCING_ROW_SPAN cells and the f0/f1 pair
// is GKR_DIM_REDUCING_PAIR_STRIDE apart.
static constexpr unsigned GKR_DIM_REDUCING_ROW_SPAN = 4;
static constexpr unsigned GKR_DIM_REDUCING_PAIR_STRIDE = 2;

template <typename E> struct gkr_ext_initial_source {
  const E *start;
};

template <typename E> struct gkr_ext_continuing_source {
  const E *previous_layer_start;
  E *this_layer_start;
  bool first_access;
};

// One slot per OutputType; `enabled_mask` selects the ones this circuit uses.
// Kept in lockstep with the Rust mirror by `compact_cuda_constants_match_rust`.
static constexpr unsigned GKR_DIM_REDUCING_SLOTS = 5;
static constexpr unsigned GKR_DIM_REDUCING_INPUTS_PER_SLOT = 2;
static constexpr unsigned GKR_DIM_REDUCING_OUTPUTS_PER_SLOT = 2;
static constexpr unsigned GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN = GKR_DIM_REDUCING_SLOTS * GKR_DIM_REDUCING_OUTPUTS_PER_SLOT;
static constexpr unsigned GKR_BACKWARD_MAX_TRACE_LEN_LOG2 = 24;
// Dim-reducing stores folding_steps - 1 round challenges plus 3 transcript challenges.
static constexpr unsigned GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 2;
// Main layers store folding_steps - 1 round challenges plus 2 transcript challenges.
static constexpr unsigned GKR_MAIN_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 1;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK = 8;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_BLOCK = 1u << GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS = GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK;
static constexpr unsigned GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS = 11;
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

// Slot index == OutputType discriminant, so a slot's kind is a compile-time
// property of its index rather than wire data.
enum gkr_dim_reducing_slot_index : u32 {
  GKR_DIM_REDUCING_SLOT_PERMUTATION_PRODUCT = 0,
  GKR_DIM_REDUCING_SLOT_LOOKUP_16_BITS = 1,
  GKR_DIM_REDUCING_SLOT_LOOKUP_TIMESTAMPS = 2,
  GKR_DIM_REDUCING_SLOT_GENERIC_LOOKUP = 3,
  GKR_DIM_REDUCING_SLOT_INITS_AND_TEARDOWNS_PRODUCT = 4,
};

// Slots whose two inputs are independent product towers; the rest are one
// coupled numerator/denominator fraction tower.
static constexpr u32 GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK =
    (1u << GKR_DIM_REDUCING_SLOT_PERMUTATION_PRODUCT) | (1u << GKR_DIM_REDUCING_SLOT_INITS_AND_TEARDOWNS_PRODUCT);

// The 4-bit pointer index in each source encoding addresses this table.
constexpr unsigned GKR_DIM_REDUCING_BASE_SLOTS = 16;

struct gkr_dim_reducing_tables {
  const u8 *bases[GKR_DIM_REDUCING_BASE_SLOTS];
  u32 log2_stride[GKR_DIM_REDUCING_BASE_SLOTS];
};

struct gkr_source_record {
  u16 src;
  u16 cache;
};

// The host packs batch exponents densely over enabled slots in verifier order.
struct gkr_dim_reducing_slot {
  gkr_source_record inputs[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
  u16 batch_exp[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
};

template <typename E> struct gkr_dim_reducing_batch {
  u32 enabled_mask;
  u32 reserved0;
  const E *eq_low;
  gkr_eq_sizes eq_sizes;
  u32 eq_sizes_pad;
  gkr_dim_reducing_tables tables;
  gkr_dim_reducing_slot slots[GKR_DIM_REDUCING_SLOTS];
  u32 slots_pad;
};

static_assert(alignof(gkr_dim_reducing_slot) == 2 && sizeof(gkr_dim_reducing_slot) == 12, "dim-reducing slot ABI drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_slot, inputs) == 0 && __builtin_offsetof(gkr_dim_reducing_slot, batch_exp) == 8,
              "dim-reducing slot offsets drift");
static_assert(alignof(gkr_dim_reducing_tables) == 8 && sizeof(gkr_dim_reducing_tables) == 192, "dim-reducing tables ABI drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_tables, bases) == 0 && __builtin_offsetof(gkr_dim_reducing_tables, log2_stride) == 128,
              "dim-reducing table offsets drift");
static_assert(alignof(gkr_source_record) == 2 && sizeof(gkr_source_record) == 4, "source record ABI drift");
static_assert(__builtin_offsetof(gkr_source_record, src) == 0 && __builtin_offsetof(gkr_source_record, cache) == 2, "source record offsets drift");
// Merged tower batch (blockIdx.y selects the pair). A pair's two streams are either two
// independent product towers (PAIRWISE2) or one lookup tower's num/den (LOOKUP). The kind
// is not per-pair wire data: `pairwise_mask` carries one bit per pair index, so pairs stay
// densely packed and the grid's y extent stays `pair_count`. The PAIRWISE2 / LOOKUP tags
// remain the shared vocabulary of the forward VM's own reduction-pair descriptor.
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_PAIR_CAP = 5;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_PAIRWISE2 = 0;
static constexpr unsigned GKR_DIM_REDUCING_FORWARD_TOWER_LOOKUP = 1;

template <typename E> struct gkr_dim_reducing_forward_tower_pair {
  const E *input[2];
  E *round_outputs[GKR_DIM_REDUCING_FORWARD_TOWER_MAX_ROUNDS][2];
};

template <typename E> struct gkr_dim_reducing_forward_tower_batch {
  gkr_dim_reducing_forward_tower_pair<E> pairs[GKR_DIM_REDUCING_FORWARD_TOWER_PAIR_CAP];
  u32 pair_count;
  u32 input_len;
  u32 round_count;
  u32 pairwise_mask;
};

static constexpr unsigned GKR_TIMESTAMP_COLUMNS_NUM_BITS = 19;

} // namespace airbender::gkr
