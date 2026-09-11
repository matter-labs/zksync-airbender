#pragma once

#include "../support/lookup_helpers.cuh"
#include "mega_finalize.cuh"

namespace airbender::gkr::backward {

constexpr unsigned GKR_DR_TAIL_MAX_SOURCES = 10;
constexpr unsigned GKR_DR_TAIL_ENTRY_CHALLENGES = 3;
constexpr unsigned GKR_DR_TAIL_BLOCK_THREADS = 256;
constexpr unsigned GKR_DR_TAIL_MAX_REMAINING_ROUNDS = 8;
constexpr unsigned GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE = 128;

static_assert((1u << (GKR_DR_TAIL_MAX_REMAINING_ROUNDS - 1)) == GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE, "DR-tail first-round accumulator bound drift");
static_assert(2 * GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE == GKR_DR_TAIL_BLOCK_THREADS, "DR-tail tested cap-eight geometry drift");

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

struct gkr_dr_tail_shared_eq_reader {
  const e4 *groups;
  gkr_eq_sizes sizes;
  unsigned group_count;

  DEVICE_FORCEINLINE e4 operator()(const unsigned row) const {
    e4 result = e4::ONE();
    if (sizes.high[0] != 0) {
      const unsigned shift = sizes.high[1] + sizes.low;
      const unsigned index = (row >> shift) & ((1u << sizes.high[0]) - 1u);
      result = e4::mul(result, groups[index]);
    }
    if (sizes.high[1] != 0) {
      const unsigned index = (row >> sizes.low) & ((1u << sizes.high[1]) - 1u);
      result = e4::mul(result, groups[GKR_EQ_GROUP_TABLE_LEN + index]);
    }
    if (sizes.low != 0) {
      const unsigned index = row & ((1u << sizes.low) - 1u);
      result = e4::mul(result, groups[(group_count - 1) * GKR_EQ_GROUP_TABLE_LEN + index]);
    }
    return result;
  }
};

DEVICE_FORCEINLINE e4 *gkr_dr_tail_active_eq_slot(e4 *groups, const unsigned group_count, const gkr_eq_sizes &sizes, unsigned &size) {
  if (sizes.low != 0) {
    size = sizes.low;
    return groups + (group_count - 1) * GKR_EQ_GROUP_TABLE_LEN;
  }
  if (sizes.high[1] != 0) {
    size = sizes.high[1];
    return groups + GKR_EQ_GROUP_TABLE_LEN;
  }
  if (sizes.high[0] != 0) {
    size = sizes.high[0];
    return groups;
  }
  size = 0;
  return groups;
}

DEVICE_FORCEINLINE void gkr_dr_tail_record_eq_fold(gkr_eq_sizes &sizes) {
  if (sizes.low != 0)
    --sizes.low;
  else if (sizes.high[1] != 0)
    --sizes.high[1];
  else
    --sizes.high[0];
}

// Tail working columns use the scalar relation helpers and source-local indexing.
DEVICE_FORCEINLINE void gkr_dr_tail_evaluate_pairwise(const e4 *state, const unsigned source_stride, const gkr_dr_tail_slot &slot, const unsigned row,
                                                      e4 &partial0, e4 &partial1) {
  const unsigned cell = GKR_DIM_REDUCING_ROW_SPAN * row;
#pragma unroll
  for (unsigned input = 0; input < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++input) {
    const e4 *source = state + static_cast<size_t>(slot.input_source[input]) * source_stride;
    const e4 even0 = source[cell];
    const e4 odd0 = source[cell + 1];
    const e4 even_delta = e4::sub(source[cell + GKR_DIM_REDUCING_PAIR_STRIDE], even0);
    const e4 odd_delta = e4::sub(source[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], odd0);
    const e4 batch_challenge = ::ab_gkr_dim_reducing_batch_challenge_table[slot.batch_exp[input]];
    e4 value0;
    e4 value1;
    gkr_eval_product(even0, odd0, value0);
    gkr_eval_product(even_delta, odd_delta, value1);
    partial0 = e4::fma(batch_challenge, value0, partial0);
    partial1 = e4::fma(batch_challenge, value1, partial1);
  }
}

DEVICE_FORCEINLINE void gkr_dr_tail_evaluate_lookup(const e4 *state, const unsigned source_stride, const gkr_dr_tail_slot &slot, const unsigned row,
                                                    e4 &partial0, e4 &partial1) {
  const unsigned cell = GKR_DIM_REDUCING_ROW_SPAN * row;
  const e4 *a = state + static_cast<size_t>(slot.input_source[0]) * source_stride;
  const e4 *b = state + static_cast<size_t>(slot.input_source[1]) * source_stride;
  const e4 a0 = a[cell];
  const e4 b0 = b[cell];
  const e4 c0 = a[cell + 1];
  const e4 d0 = b[cell + 1];
  const e4 a1 = e4::sub(a[cell + GKR_DIM_REDUCING_PAIR_STRIDE], a0);
  const e4 b1 = e4::sub(b[cell + GKR_DIM_REDUCING_PAIR_STRIDE], b0);
  const e4 c1 = e4::sub(a[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], c0);
  const e4 d1 = e4::sub(b[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], d0);
  e4 num0;
  e4 den0;
  e4 num1;
  e4 den1;
  gkr_eval_lookup_pair(a0, b0, c0, d0, num0, den0);
  gkr_eval_lookup_pair(a1, b1, c1, d1, num1, den1);
  const e4 batch0 = ::ab_gkr_dim_reducing_batch_challenge_table[slot.batch_exp[0]];
  const e4 batch1 = ::ab_gkr_dim_reducing_batch_challenge_table[slot.batch_exp[1]];
  partial0 = e4::fma(batch0, num0, e4::fma(batch1, den0, partial0));
  partial1 = e4::fma(batch0, num1, e4::fma(batch1, den1, partial1));
}

DEVICE_FORCEINLINE e4 dr_tail_cooperative_round_with_inverses(const e4 e, const e4 c, const e4 rho, const e4 inv_eq, const e4 inv_rho, u32 *seed, e4 *claim,
                                                              e4 *eq, e4 *coeffs_out) {
  using namespace ::airbender::gkr::ops;
  const e4 normalized = e4::mul(*claim, inv_eq);
  const e4 b = e4::sub(e4::ONE(), rho), a = e4::sub(e4::dbl(rho), e4::ONE());
  const e4 be = e4::mul(b, e);
  e4 d = e4::sub(normalized, be);
  d = e4::mul(d, inv_rho);
  d = e4::sub(d, c);
  d = e4::sub(d, e);
  const e4 coeffs[4] = {be, e4::add(e4::mul(a, e), e4::mul(b, d)), e4::add(e4::mul(a, d), e4::mul(b, c)), e4::mul(a, c)};
#pragma unroll
  for (u32 i = 0; i < 4; ++i)
    coeffs_out[i] = coeffs[i];
  const e4 challenge = commit_quadratic_and_draw_challenge(seed, coeffs);
  *claim = eval_degree3_poly(coeffs, challenge);
  *eq = eq_poly(challenge, rho);
  return challenge;
}

DEVICE_FORCEINLINE e4 dr_tail_cooperative_warp_sum(e4 value) {
#pragma unroll
  for (unsigned offset = 16; offset != 0; offset >>= 1) {
    e4 other;
#pragma unroll
    for (unsigned limb = 0; limb < 4; ++limb)
      reinterpret_cast<u32 *>(&other)[limb] = __shfl_xor_sync(0xffffffffu, reinterpret_cast<const u32 *>(&value)[limb], offset);
    value = e4::add(value, other);
  }
  return value;
}

template <unsigned BLOCK_THREADS>
DEVICE_FORCEINLINE void dr_tail_cooperative_finalize(e4 c0, e4 c1, const unsigned active_partials, const e4 *prev_claim_coord, u32 *seed_io, e4 *claim_io,
                                                     e4 *eq_prefactor_io, e4 *coeffs_out, e4 *challenge_out, e4 *active_eq_slot_base,
                                                     const unsigned active_eq_size_before_fold) {
  static_assert(BLOCK_THREADS >= 256 && BLOCK_THREADS <= 1024 && BLOCK_THREADS % 32 == 0);
  constexpr unsigned WARPS = BLOCK_THREADS / 32;
  __shared__ e4 warp_c0[WARPS];
  __shared__ e4 warp_c1[WARPS];
  __shared__ e4 inverses[2];
  const unsigned tid = threadIdx.x;
  const unsigned lane = tid & 31;
  const unsigned warp = tid >> 5;
  const unsigned partial_warps = (active_partials + 31) / 32;
  const unsigned active_warps = partial_warps < WARPS ? partial_warps : WARPS;
  if (warp < active_warps) {
    c0 = dr_tail_cooperative_warp_sum(c0);
    c1 = dr_tail_cooperative_warp_sum(c1);
    if (lane == 0) {
      warp_c0[warp] = c0;
      warp_c1[warp] = c1;
    }
  }
  __syncthreads();
  if (warp == 0) {
    c0 = dr_tail_cooperative_warp_sum(lane < active_warps ? warp_c0[lane] : e4::ZERO());
    c1 = dr_tail_cooperative_warp_sum(lane < active_warps ? warp_c1[lane] : e4::ZERO());
    if (lane < 2)
      inverses[lane] = e4::inv(lane == 0 ? *eq_prefactor_io : *prev_claim_coord);
    __syncwarp();
    if (lane == 0) {
      const e4 prev_coord = *prev_claim_coord;
      *challenge_out = dr_tail_cooperative_round_with_inverses(c0, c1, prev_coord, inverses[0], inverses[1], seed_io, claim_io, eq_prefactor_io, coeffs_out);
    }
  }
  fold_active_eq_slot<BLOCK_THREADS>(active_eq_slot_base, active_eq_size_before_fold);
}

template <unsigned BLOCK_THREADS> DEVICE_FORCEINLINE void dr_tail_cooperative_inner(const gkr_dr_tail_megakernel_desc &desc, e4 *global_state) {
  extern __shared__ __align__(32) unsigned char dynamic_smem[];
  e4 *state = global_state;

  const unsigned tid = threadIdx.x;
  const unsigned remaining_rounds = desc.folding_steps - desc.entry_round;
  const unsigned entry_rows = 1u << remaining_rounds;
  const unsigned source_stride = entry_rows * GKR_DIM_REDUCING_PAIR_STRIDE;
  e4 *next_state = state + static_cast<size_t>(desc.source_count) * source_stride;
  e4 *const eq_groups = reinterpret_cast<e4 *>(dynamic_smem);
  const unsigned eq_challenge_count = remaining_rounds - 1;
  const unsigned eq_group_count = gkr_eq_group_count(eq_challenge_count);

  __shared__ e4 entry_weights[1u << GKR_DR_TAIL_ENTRY_CHALLENGES];
  // Keep the entry challenge tuple in shared memory. A thread-0 local array
  // becomes a 16-byte local-memory spill in the linked production kernel,
  // which is forbidden by the resource admission gate.
  __shared__ e4 entry_challenges[GKR_DR_TAIL_ENTRY_CHALLENGES];
  __shared__ e4 round_challenge;
  __shared__ gkr_eq_sizes eq_sizes_shared;
  // Entry 0 starts from raw canonical pairs: no challenges have been drawn, so
  // the loader copies instead of folding.
  const bool direct_entry = desc.entry_round == 0;
  if (tid < GKR_DR_TAIL_ENTRY_CHALLENGES && !direct_entry)
    entry_challenges[tid] = load<e4, ld_modifier::cs>(desc.challenges_out, desc.entry_round - GKR_DR_TAIL_ENTRY_CHALLENGES + tid);
  __syncthreads();
  if (tid < 8 && !direct_entry) {
    e4 weight = e4::ONE();
#pragma unroll
    for (unsigned bit = 0; bit < GKR_DR_TAIL_ENTRY_CHALLENGES; ++bit) {
      const e4 factor = ((tid >> bit) & 1u) != 0 ? entry_challenges[bit] : e4::sub(e4::ONE(), entry_challenges[bit]);
      weight = e4::mul(weight, factor);
    }
    entry_weights[tid] = weight;
  }
  __syncthreads();

  for (unsigned source_idx = 0; source_idx < desc.source_count; ++source_idx) {
    const auto *source = reinterpret_cast<const gkr_dr_tail_e4_pair *>(desc.source_ptrs[source_idx]);
    auto *destination = reinterpret_cast<gkr_dr_tail_e4_pair *>(state + static_cast<size_t>(source_idx) * source_stride);
    if (direct_entry) {
      for (unsigned row = tid; row < entry_rows; row += BLOCK_THREADS)
        destination[row] = load<gkr_dr_tail_e4_pair, ld_modifier::cs>(source, row);
    } else {
      const unsigned ancestor = tid & 7;
      // Eight adjacent lanes read eight adjacent canonical ancestor pairs.
      for (unsigned base = 0; base < entry_rows; base += BLOCK_THREADS / 8) {
        const unsigned row = base + tid / 8;
        gkr_dr_tail_e4_pair folded{{e4::ZERO(), e4::ZERO()}};
        if (row < entry_rows) {
          const auto value = load<gkr_dr_tail_e4_pair, ld_modifier::cs>(source, (row << 3) + ancestor);
          folded.cells[0] = e4::mul(entry_weights[ancestor], value.cells[0]);
          folded.cells[1] = e4::mul(entry_weights[ancestor], value.cells[1]);
        }
#pragma unroll
        for (unsigned offset = 4; offset != 0; offset >>= 1) {
#pragma unroll
          for (unsigned cell = 0; cell < 2; ++cell) {
            e4 other;
#pragma unroll
            for (unsigned limb = 0; limb < 4; ++limb)
              reinterpret_cast<u32 *>(&other)[limb] = __shfl_xor_sync(0xffffffffu, reinterpret_cast<const u32 *>(&folded.cells[cell])[limb], offset, 8);
            folded.cells[cell] = e4::add(folded.cells[cell], other);
          }
        }
        if (ancestor == 0 && row < entry_rows)
          destination[row] = folded;
      }
    }
  }
  __syncthreads();

  // Rebuild exactly Eq(tau[entry_round + 1 .. folding_steps]) in shared memory.
  const gkr_shared_eq_group_table_writer<e4> shared_writer{eq_groups};
  for (unsigned group = 0; group < eq_group_count; ++group) {
    gkr_build_eq_group_table_from_point<e4>(desc.tau, desc.entry_round + 1, eq_challenge_count, group, shared_writer);
    __syncthreads();
  }
  if (tid == 0) {
    eq_sizes_shared = {};
    const unsigned groups = gkr_eq_group_count(eq_challenge_count);
    unsigned consumed = 0;
    unsigned high_idx = 0;
    for (unsigned group = 0; group < groups; ++group) {
      const unsigned remaining = eq_challenge_count - consumed;
      const unsigned group_size = remaining < GKR_EQ_GROUP_SIZE ? remaining : GKR_EQ_GROUP_SIZE;
      if (group + 1 == groups)
        eq_sizes_shared.low = group_size;
      else
        eq_sizes_shared.high[high_idx++] = group_size;
      consumed += group_size;
    }
  }
  __syncthreads();
  gkr_eq_sizes &eq_sizes = eq_sizes_shared;

  unsigned current_cells = source_stride;
#pragma unroll 1
  for (unsigned round = desc.entry_round; round < desc.folding_steps; ++round) {
    const unsigned acc_size = current_cells / GKR_DIM_REDUCING_ROW_SPAN;
    e4 thread_partial0 = e4::ZERO();
    e4 thread_partial1 = e4::ZERO();
    const gkr_dr_tail_shared_eq_reader eq_reader{eq_groups, eq_sizes, eq_group_count};
    for (unsigned row = tid; row < acc_size; row += BLOCK_THREADS) {
      e4 row_partial0 = e4::ZERO();
      e4 row_partial1 = e4::ZERO();
#pragma unroll 1
      for (unsigned slot_idx = 0; slot_idx < GKR_DIM_REDUCING_SLOTS; ++slot_idx) {
        if ((desc.enabled_mask & (1u << slot_idx)) == 0)
          continue;
        const gkr_dr_tail_slot &slot = desc.slots[slot_idx];
        if (((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK >> slot_idx) & 1u) != 0)
          gkr_dr_tail_evaluate_pairwise(state, source_stride, slot, row, row_partial0, row_partial1);
        else
          gkr_dr_tail_evaluate_lookup(state, source_stride, slot, row, row_partial0, row_partial1);
      }
      const e4 eq = eq_reader(row);
      thread_partial0 = e4::fma(eq, row_partial0, thread_partial0);
      thread_partial1 = e4::fma(eq, row_partial1, thread_partial1);
    }

    const bool final_round = round + 1 == desc.folding_steps;
    unsigned active_eq_size = 0;
    e4 *const active_eq_slot = final_round ? eq_groups : gkr_dr_tail_active_eq_slot(eq_groups, eq_group_count, eq_sizes, active_eq_size);
    dr_tail_cooperative_finalize<BLOCK_THREADS>(thread_partial0, thread_partial1, acc_size, desc.tau + round, desc.seed, desc.claim, desc.eq_prefactor,
                                                desc.coeffs_out + 4 * round, &round_challenge, active_eq_slot, active_eq_size);
    __syncthreads();

    // The finalizer reads tau[round] before publishing this challenge.
    if (tid == 0)
      desc.challenges_out[round] = round_challenge;
    __syncthreads();

    if (!final_round) {
      // The finalizer folded exactly one slot; mirror the same low > high[1] > high[0] transition.
      if (tid == 0)
        gkr_dr_tail_record_eq_fold(eq_sizes);
      __syncthreads();
      const unsigned next_cells = current_cells / 2;
      // Each output goes to the other buffer; readers never overlap writers.
      for (unsigned index = tid; index < desc.source_count * next_cells; index += BLOCK_THREADS) {
        const unsigned source_idx = index / next_cells;
        const unsigned cell = index % next_cells;
        const e4 *const source = state + static_cast<size_t>(source_idx) * source_stride;
        const unsigned ancestor = gkr_dim_reducing_ancestor_index(cell);
        const e4 f0 = source[ancestor];
        const e4 f1 = source[ancestor + GKR_DIM_REDUCING_PAIR_STRIDE];
        next_state[static_cast<size_t>(source_idx) * source_stride + cell] = e4::fma(round_challenge, e4::sub(f1, f0), f0);
      }
      __syncthreads();
      e4 *const previous = state;
      state = next_state;
      next_state = previous;
      current_cells = next_cells;
    }
  }

  // The unchanged epilogue consumes four pre-LSB cells per canonical source.
  for (unsigned cell = tid; cell < desc.source_count * 4; cell += BLOCK_THREADS) {
    const unsigned source_idx = cell / 4;
    const unsigned source_cell = cell % 4;
    store<e4, st_modifier::cs>(desc.final_sources, state[static_cast<size_t>(source_idx) * source_stride + source_cell], cell);
  }
}

} // namespace airbender::gkr::backward
