#pragma once

#include "../../backward/dr_tail_shared.cuh"

#include "../../support/lookup_helpers.cuh"
#include "batch_challenges_pr.cuh"
#include "tail_common_pr.cuh"

namespace airbender::gkr::proth120::backward {

using pr = ::airbender::primitives::field::proth120;

constexpr unsigned PR_DR_TAIL_MAX_SOURCES = 10;
constexpr unsigned PR_DR_TAIL_ENTRY_CHALLENGES = 3;
constexpr unsigned PR_DR_TAIL_BLOCK_THREADS = 256;
constexpr unsigned PR_DR_TAIL_MAX_REMAINING_ROUNDS = 8;
constexpr unsigned PR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE = 128;

static_assert((1u << (PR_DR_TAIL_MAX_REMAINING_ROUNDS - 1)) == PR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE, "Proth120 DR-tail first-round accumulator bound drift");
static_assert(2 * PR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE == PR_DR_TAIL_BLOCK_THREADS, "Proth120 DR-tail first contraction must assign one cell per thread");
static_assert(sizeof(pr) == 16 && alignof(pr) == 16, "Proth120 element ABI drift");

struct pr_dr_tail_slot {
  u16 input_source[GKR_DIM_REDUCING_INPUTS_PER_SLOT];
  u16 batch_exp[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT];
};

struct pr_dr_tail_megakernel_desc {
  u32 enabled_mask;
  u32 folding_steps;
  u32 entry_round;
  u32 source_count;
  const pr *source_ptrs[PR_DR_TAIL_MAX_SOURCES];
  pr *final_sources;
  const pr *tau;
  u8 *seed;
  pr *claim;
  pr *eq_prefactor;
  pr *coeffs_out;
  pr *challenges_out;
  pr_dr_tail_slot slots[GKR_DIM_REDUCING_SLOTS];
};

static_assert(alignof(pr_dr_tail_slot) == 2 && sizeof(pr_dr_tail_slot) == 8, "Proth120 DR-tail slot ABI drift");
static_assert(__builtin_offsetof(pr_dr_tail_slot, input_source) == 0 && __builtin_offsetof(pr_dr_tail_slot, batch_exp) == 4,
              "Proth120 DR-tail slot offsets drift");
static_assert(alignof(pr_dr_tail_megakernel_desc) == 8 && sizeof(pr_dr_tail_megakernel_desc) == 192, "Proth120 DR-tail descriptor ABI drift");
static_assert(__builtin_offsetof(pr_dr_tail_megakernel_desc, enabled_mask) == 0 && __builtin_offsetof(pr_dr_tail_megakernel_desc, folding_steps) == 4 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, entry_round) == 8 && __builtin_offsetof(pr_dr_tail_megakernel_desc, source_count) == 12 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, source_ptrs) == 16 && __builtin_offsetof(pr_dr_tail_megakernel_desc, final_sources) == 96 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, tau) == 104 && __builtin_offsetof(pr_dr_tail_megakernel_desc, seed) == 112 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, claim) == 120 && __builtin_offsetof(pr_dr_tail_megakernel_desc, eq_prefactor) == 128 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, coeffs_out) == 136 && __builtin_offsetof(pr_dr_tail_megakernel_desc, challenges_out) == 144 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, slots) == 152,
              "Proth120 DR-tail descriptor offsets drift");
static_assert(sizeof(pr_dr_tail_megakernel_desc) + sizeof(pr *) == 200, "Proth120 DR-tail complete argument drift");
static_assert(std::is_standard_layout_v<pr_dr_tail_megakernel_desc> && std::is_trivially_copyable_v<pr_dr_tail_megakernel_desc>,
              "Proth120 DR-tail descriptor must be a plain record");

struct __align__(32) pr_dr_tail_pair {
  pr cells[2];
};

static_assert(sizeof(pr_dr_tail_pair) == 32 && alignof(pr_dr_tail_pair) == 32, "Proth120 DR-tail pair ABI drift");
static_assert(sizeof(pr_dr_tail_pair) == GKR_DIM_REDUCING_PAIR_STRIDE * sizeof(pr), "Proth120 DR-tail pair indexing assumes the pair stride");

struct dr_tail_policy {
  using Field = pr;
  using Desc = pr_dr_tail_megakernel_desc;
  using Slot = pr_dr_tail_slot;
  using Pair = pr_dr_tail_pair;
  using SeedWord = u8;
  static constexpr unsigned THREADS = 256;
  static constexpr unsigned ENTRY_CHALLENGES = 3;
  static DEVICE_FORCEINLINE Field batch(const Desc &desc, unsigned exp) { return ::ab_pr_gkr_dim_reducing_batch_challenge_table[exp]; }
  static DEVICE_FORCEINLINE Field shuffle_value(Field value, unsigned offset) { return shfl_xor(0xffffffffu, value, offset, 8); }
  static DEVICE_FORCEINLINE void build_eq_group(const Field *point, unsigned offset, unsigned count, unsigned group, Field *groups) {
    const gkr_shared_eq_group_table_writer<Field> writer{groups};
    gkr_build_eq_group_table_from_point<Field>(point, offset, count, group, writer);
  }
  static DEVICE_FORCEINLINE Field round_update(Field c0, Field c1, Field prev, Field inv_eq, Field inv_prev, SeedWord *seed, Field *claim, Field *eq,
                                               Field *coeffs) {
    return run_round_update_with_inverses_pr(c0, c1, prev, inv_eq, inv_prev, seed, claim, eq, coeffs);
  }
  static DEVICE_FORCEINLINE void fold_eq(Field *slot, unsigned size) { ::airbender::gkr::backward::fold_active_eq_slot<THREADS>(slot, size); }
};

DEVICE_FORCEINLINE void pr_dr_tail_inner(const pr_dr_tail_megakernel_desc &desc, pr *global_state) {
  ::airbender::gkr::dr_tail_detail::inner<dr_tail_policy>(desc, global_state);
}

} // namespace airbender::gkr::proth120::backward
