#pragma once

#include "gkr/support/descriptors.cuh"
#include "primitives/baby_bear/field.cuh"

using namespace ::airbender::primitives::field;

namespace airbender::gkr {

static_assert(alignof(gkr_dim_reducing_batch<e4>) == 8 && sizeof(gkr_dim_reducing_batch<e4>) == 288, "dim-reducing descriptor ABI drift");
static_assert(__builtin_offsetof(gkr_dim_reducing_batch<e4>, enabled_mask) == 0 && __builtin_offsetof(gkr_dim_reducing_batch<e4>, reserved0) == 4 &&
                  __builtin_offsetof(gkr_dim_reducing_batch<e4>, eq_low) == 8 && __builtin_offsetof(gkr_dim_reducing_batch<e4>, eq_sizes) == 16 &&
                  __builtin_offsetof(gkr_dim_reducing_batch<e4>, eq_sizes_pad) == 28 && __builtin_offsetof(gkr_dim_reducing_batch<e4>, tables) == 32 &&
                  __builtin_offsetof(gkr_dim_reducing_batch<e4>, slots) == 224 && __builtin_offsetof(gkr_dim_reducing_batch<e4>, slots_pad) == 284,
              "dim-reducing descriptor offsets drift");
static_assert(sizeof(gkr_dim_reducing_batch<e4>) + 2 * sizeof(u32) <= 32764, "dim-reducing kernel parameters exceed CUDA limit");

static_assert(sizeof(gkr_dim_reducing_forward_tower_pair<e4>) == 144, "tower pair ABI size drift");
static_assert(sizeof(gkr_dim_reducing_forward_tower_batch<e4>) == 736, "tower batch ABI size drift");
static_assert(alignof(gkr_dim_reducing_forward_tower_batch<e4>) == 8, "tower batch ABI alignment drift");

struct gkr_forward_setup_generic_lookup_descriptor {
  const bf *input;
};

template <typename E> struct gkr_forward_setup_generic_lookup_batch {
  u32 column_count;
  u32 decoder_table_id;
  bf padding_value;
  E *output;
  E *decoder_fill_value_out;
  E *padding_fill_value_out;
  gkr_forward_setup_generic_lookup_descriptor descriptors[GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
};

static_assert(alignof(gkr_forward_setup_generic_lookup_batch<e4>) == 8 && sizeof(gkr_forward_setup_generic_lookup_batch<e4>) == 128,
              "setup generic lookup batch ABI drift");
static_assert(__builtin_offsetof(gkr_forward_setup_generic_lookup_batch<e4>, decoder_table_id) == 4 &&
                  __builtin_offsetof(gkr_forward_setup_generic_lookup_batch<e4>, padding_value) == 8 &&
                  __builtin_offsetof(gkr_forward_setup_generic_lookup_batch<e4>, output) == 16 &&
                  __builtin_offsetof(gkr_forward_setup_generic_lookup_batch<e4>, decoder_fill_value_out) == 24 &&
                  __builtin_offsetof(gkr_forward_setup_generic_lookup_batch<e4>, padding_fill_value_out) == 32 &&
                  __builtin_offsetof(gkr_forward_setup_generic_lookup_batch<e4>, descriptors) == 40,
              "setup generic lookup batch offsets drift");

} // namespace airbender::gkr

// __constant__ batch-challenge table for dim-reducing backward compact kernels.
// Defined in backward/dim_reducing.cu.
EXTERN __device__ __constant__ e4 ab_gkr_dim_reducing_batch_challenge_table[airbender::gkr::GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_dim_reducing_layer_claim_point[airbender::gkr::GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
EXTERN __device__ __constant__ e4 ab_gkr_lookup_alpha_powers[airbender::gkr::GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS];
