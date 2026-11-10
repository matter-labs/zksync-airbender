#pragma once

#include "dr_tail_shared.cuh"

#include "../support/lookup_helpers.cuh"
#include "tail_common.cuh"

namespace airbender::gkr::backward {

constexpr unsigned GKR_DR_TAIL_MAX_SOURCES = 10;
constexpr unsigned GKR_DR_TAIL_ENTRY_CHALLENGES = 3;
constexpr unsigned GKR_DR_TAIL_BLOCK_THREADS = 256;
constexpr unsigned GKR_DR_TAIL_MAX_REMAINING_ROUNDS = 8;
constexpr unsigned GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE = 128;

static_assert((1u << (GKR_DR_TAIL_MAX_REMAINING_ROUNDS - 1)) == GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE, "DR-tail first-round accumulator bound drift");
static_assert(2 * GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE == GKR_DR_TAIL_BLOCK_THREADS,
              "DR-tail first contraction must assign at most one destination cell per thread");

struct gkr_dr_tail_slot {
  u16 input_source[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
  u16 batch_exp[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
};

struct gkr_dr_tail_megakernel_desc {
  u32 enabled_mask;
  u32 folding_steps;
  u32 entry_round;
  u32 source_count;
  const e4 *source_ptrs[GKR_DR_TAIL_MAX_SOURCES];
  e4 *final_sources;
  const e4 *tau;
  u32 *seed;
  e4 *claim;
  e4 *eq_prefactor;
  e4 *coeffs_out;
  e4 *challenges_out;
  gkr_dr_tail_slot slots[GKR_DIM_REDUCING_SLOTS];
};

static_assert(alignof(gkr_dr_tail_slot) == 2 && sizeof(gkr_dr_tail_slot) == 8, "DR-tail slot ABI drift");
static_assert(__builtin_offsetof(gkr_dr_tail_slot, input_source) == 0 && __builtin_offsetof(gkr_dr_tail_slot, batch_exp) == 4, "DR-tail slot offsets drift");
static_assert(alignof(gkr_dr_tail_megakernel_desc) == 8 && sizeof(gkr_dr_tail_megakernel_desc) == 192, "DR-tail descriptor ABI drift");
static_assert(__builtin_offsetof(gkr_dr_tail_megakernel_desc, enabled_mask) == 0 && __builtin_offsetof(gkr_dr_tail_megakernel_desc, folding_steps) == 4 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, entry_round) == 8 && __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_count) == 12 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) == 16 && __builtin_offsetof(gkr_dr_tail_megakernel_desc, final_sources) == 96 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, tau) == 104 && __builtin_offsetof(gkr_dr_tail_megakernel_desc, seed) == 112 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, claim) == 120 && __builtin_offsetof(gkr_dr_tail_megakernel_desc, eq_prefactor) == 128 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, coeffs_out) == 136 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, challenges_out) == 144 && __builtin_offsetof(gkr_dr_tail_megakernel_desc, slots) == 152,
              "DR-tail descriptor offsets drift");
static_assert(__builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 0 * sizeof(const e4 *) == 16 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 1 * sizeof(const e4 *) == 24 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 2 * sizeof(const e4 *) == 32 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 3 * sizeof(const e4 *) == 40 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 4 * sizeof(const e4 *) == 48 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 5 * sizeof(const e4 *) == 56 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 6 * sizeof(const e4 *) == 64 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 7 * sizeof(const e4 *) == 72 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 8 * sizeof(const e4 *) == 80 &&
                  __builtin_offsetof(gkr_dr_tail_megakernel_desc, source_ptrs) + 9 * sizeof(const e4 *) == 88,
              "DR-tail source pointer offsets drift");
static_assert(sizeof(gkr_dr_tail_megakernel_desc) + sizeof(e4 *) <= 32764, "DR-tail kernel parameters exceed CUDA limit");

struct __align__(32) gkr_dr_tail_e4_pair {
  e4 cells[2];
};

static_assert(sizeof(gkr_dr_tail_e4_pair) == 32 && alignof(gkr_dr_tail_e4_pair) == 32, "DR-tail packed E4 pair ABI drift");
static_assert(sizeof(gkr_dr_tail_e4_pair) == GKR_DIM_REDUCING_PAIR_STRIDE * sizeof(e4), "DR-tail pair indexing assumes the pair stride");

// Tail working columns use the scalar relation helpers and source-local indexing.
struct dr_tail_policy {
  using Field = e4;
  using Desc = gkr_dr_tail_megakernel_desc;
  using Slot = gkr_dr_tail_slot;
  using Pair = gkr_dr_tail_e4_pair;
  using SeedWord = u32;
  static constexpr unsigned THREADS = 256;
  static constexpr unsigned ENTRY_CHALLENGES = 3;
  static DEVICE_FORCEINLINE Field batch(const Desc &desc, unsigned exp) { return ::ab_gkr_dim_reducing_batch_challenge_table[exp]; }
  static DEVICE_FORCEINLINE Field shuffle_value(Field value, unsigned offset) {
    e4 other;
#pragma unroll
    for (unsigned limb = 0; limb < 4; ++limb)
      reinterpret_cast<u32 *>(&other)[limb] = __shfl_xor_sync(0xffffffffu, reinterpret_cast<const u32 *>(&value)[limb], offset, 8);
    return other;
  }
  static DEVICE_FORCEINLINE void build_eq_group(const Field *point, unsigned offset, unsigned count, unsigned group, Field *groups) {
    const gkr_shared_eq_group_table_writer<e4> writer{groups};
    gkr_build_eq_group_table_from_point<e4>(point, offset, count, group, writer);
  }
  static DEVICE_FORCEINLINE Field round_update(Field c0, Field c1, Field prev, Field inv_eq, Field inv_prev, SeedWord *seed, Field *claim, Field *eq,
                                               Field *coeffs) {
    return run_round_update_with_inverses(c0, c1, prev, inv_eq, inv_prev, seed, claim, eq, coeffs);
  }
  static DEVICE_FORCEINLINE void fold_eq(Field *slot, unsigned size) { fold_active_eq_slot<THREADS>(slot, size); }
};

DEVICE_FORCEINLINE void dr_tail_cooperative_inner(const gkr_dr_tail_megakernel_desc &desc, e4 *global_state) {
  ::airbender::gkr::dr_tail_detail::inner<dr_tail_policy>(desc, global_state);
}

} // namespace airbender::gkr::backward
