#pragma once

#include "../../support/lookup_helpers.cuh"
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
  const pr *batch_challenges;
  pr_dr_tail_slot slots[GKR_DIM_REDUCING_SLOTS];
};

static_assert(alignof(pr_dr_tail_slot) == 2 && sizeof(pr_dr_tail_slot) == 8, "Proth120 DR-tail slot ABI drift");
static_assert(__builtin_offsetof(pr_dr_tail_slot, input_source) == 0 && __builtin_offsetof(pr_dr_tail_slot, batch_exp) == 4,
              "Proth120 DR-tail slot offsets drift");
static_assert(alignof(pr_dr_tail_megakernel_desc) == 8 && sizeof(pr_dr_tail_megakernel_desc) == 200, "Proth120 DR-tail descriptor ABI drift");
static_assert(__builtin_offsetof(pr_dr_tail_megakernel_desc, enabled_mask) == 0 && __builtin_offsetof(pr_dr_tail_megakernel_desc, folding_steps) == 4 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, entry_round) == 8 && __builtin_offsetof(pr_dr_tail_megakernel_desc, source_count) == 12 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, source_ptrs) == 16 && __builtin_offsetof(pr_dr_tail_megakernel_desc, final_sources) == 96 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, tau) == 104 && __builtin_offsetof(pr_dr_tail_megakernel_desc, seed) == 112 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, claim) == 120 && __builtin_offsetof(pr_dr_tail_megakernel_desc, eq_prefactor) == 128 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, coeffs_out) == 136 && __builtin_offsetof(pr_dr_tail_megakernel_desc, challenges_out) == 144 &&
                  __builtin_offsetof(pr_dr_tail_megakernel_desc, batch_challenges) == 152 && __builtin_offsetof(pr_dr_tail_megakernel_desc, slots) == 160,
              "Proth120 DR-tail descriptor offsets drift");
static_assert(sizeof(pr_dr_tail_megakernel_desc) + sizeof(pr *) == 208, "Proth120 DR-tail complete argument drift");
static_assert(std::is_standard_layout_v<pr_dr_tail_megakernel_desc> && std::is_trivially_copyable_v<pr_dr_tail_megakernel_desc>,
              "Proth120 DR-tail descriptor must be a plain record");

struct __align__(32) pr_dr_tail_pair {
  pr cells[2];
};

static_assert(sizeof(pr_dr_tail_pair) == 32 && alignof(pr_dr_tail_pair) == 32, "Proth120 DR-tail pair ABI drift");
static_assert(sizeof(pr_dr_tail_pair) == GKR_DIM_REDUCING_PAIR_STRIDE * sizeof(pr), "Proth120 DR-tail pair indexing assumes the pair stride");

struct pr_dr_tail_shared_eq_reader {
  const pr *groups;
  gkr_eq_sizes sizes;
  unsigned group_count;

  DEVICE_FORCEINLINE pr operator()(const unsigned row) const {
    pr result = pr_one();
    if (sizes.high[0] != 0) {
      const unsigned shift = sizes.high[1] + sizes.low;
      const unsigned index = (row >> shift) & ((1u << sizes.high[0]) - 1u);
      result = pr::mul(result, groups[index]);
    }
    if (sizes.high[1] != 0) {
      const unsigned index = (row >> sizes.low) & ((1u << sizes.high[1]) - 1u);
      result = pr::mul(result, groups[GKR_EQ_GROUP_TABLE_LEN + index]);
    }
    if (sizes.low != 0) {
      const unsigned index = row & ((1u << sizes.low) - 1u);
      result = pr::mul(result, groups[(group_count - 1) * GKR_EQ_GROUP_TABLE_LEN + index]);
    }
    return result;
  }
};

DEVICE_FORCEINLINE pr *pr_dr_tail_active_eq_slot(pr *groups, const unsigned group_count, const gkr_eq_sizes &sizes, unsigned &size) {
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

DEVICE_FORCEINLINE void pr_dr_tail_record_eq_fold(gkr_eq_sizes &sizes) {
  if (sizes.low != 0)
    --sizes.low;
  else if (sizes.high[1] != 0)
    --sizes.high[1];
  else
    --sizes.high[0];
}

DEVICE_FORCEINLINE void pr_dr_tail_evaluate_pairwise(const pr *state, const unsigned source_stride, const pr_dr_tail_slot &slot, const pr *batch_challenges,
                                                     const unsigned row, pr &partial0, pr &partial1) {
  const unsigned cell = GKR_DIM_REDUCING_ROW_SPAN * row;
#pragma unroll
  for (unsigned input = 0; input < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++input) {
    const pr *source = state + static_cast<size_t>(slot.input_source[input]) * source_stride;
    const pr even0 = source[cell];
    const pr odd0 = source[cell + 1];
    const pr even_delta = pr::sub(source[cell + GKR_DIM_REDUCING_PAIR_STRIDE], even0);
    const pr odd_delta = pr::sub(source[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], odd0);
    const pr batch_challenge = load<pr, ld_modifier::ca>(batch_challenges, slot.batch_exp[input]);
    pr value0;
    pr value1;
    gkr_eval_product(even0, odd0, value0);
    gkr_eval_product(even_delta, odd_delta, value1);
    partial0 = pr::fma(batch_challenge, value0, partial0);
    partial1 = pr::fma(batch_challenge, value1, partial1);
  }
}

DEVICE_FORCEINLINE void pr_dr_tail_evaluate_lookup(const pr *state, const unsigned source_stride, const pr_dr_tail_slot &slot, const pr *batch_challenges,
                                                   const unsigned row, pr &partial0, pr &partial1) {
  const unsigned cell = GKR_DIM_REDUCING_ROW_SPAN * row;
  const pr *a = state + static_cast<size_t>(slot.input_source[0]) * source_stride;
  const pr *b = state + static_cast<size_t>(slot.input_source[1]) * source_stride;
  const pr a0 = a[cell];
  const pr b0 = b[cell];
  const pr c0 = a[cell + 1];
  const pr d0 = b[cell + 1];
  const pr a1 = pr::sub(a[cell + GKR_DIM_REDUCING_PAIR_STRIDE], a0);
  const pr b1 = pr::sub(b[cell + GKR_DIM_REDUCING_PAIR_STRIDE], b0);
  const pr c1 = pr::sub(a[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], c0);
  const pr d1 = pr::sub(b[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], d0);
  pr num0;
  pr den0;
  pr num1;
  pr den1;
  gkr_eval_lookup_pair(a0, b0, c0, d0, num0, den0);
  gkr_eval_lookup_pair(a1, b1, c1, d1, num1, den1);
  const pr batch0 = load<pr, ld_modifier::ca>(batch_challenges, slot.batch_exp[0]);
  const pr batch1 = load<pr, ld_modifier::ca>(batch_challenges, slot.batch_exp[1]);
  partial0 = pr::fma(batch0, num0, pr::fma(batch1, den0, partial0));
  partial1 = pr::fma(batch0, num1, pr::fma(batch1, den1, partial1));
}

DEVICE_FORCEINLINE void pr_dr_tail_build_eq_group(const pr *claim_point, const unsigned challenge_offset, const unsigned challenge_count,
                                                  const unsigned group_idx, pr *destination) {
  const unsigned group_size = gkr_eq_group_size(challenge_count, group_idx);
  if (group_size == 0)
    return;
  const unsigned tid = threadIdx.x;
  const unsigned chunk_count = (group_size + GKR_EQ_CHUNK_SIZE - 1) / GKR_EQ_CHUNK_SIZE;
  const unsigned group_start = group_idx * GKR_EQ_GROUP_SIZE;
  __shared__ pr chunk_tables[GKR_EQ_MAX_CHUNKS_PER_GROUP][GKR_EQ_CHUNK_TABLE_LEN];
  if (tid < chunk_count * GKR_EQ_CHUNK_TABLE_LEN) {
    const unsigned chunk_idx = tid / GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned chunk_table_idx = tid % GKR_EQ_CHUNK_TABLE_LEN;
    const unsigned variable_offset = chunk_idx * GKR_EQ_CHUNK_SIZE;
    const unsigned remaining = group_size - variable_offset;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    if (chunk_table_idx < (1u << chunk_size)) {
      const unsigned first_idx = challenge_offset + challenge_count - 1 - (group_start + variable_offset);
      const unsigned first_bit = chunk_size == 2 ? ((chunk_table_idx >> 1) & 1u) : (chunk_table_idx & 1u);
      const pr first_challenge = load<pr, ld_modifier::cs>(claim_point, first_idx);
      pr value = first_bit ? first_challenge : pr::sub(pr_one(), first_challenge);
      if (chunk_size == 2) {
        const pr second_challenge = load<pr, ld_modifier::cs>(claim_point, first_idx - 1);
        value = pr::mul(value, (chunk_table_idx & 1u) ? second_challenge : pr::sub(pr_one(), second_challenge));
      }
      chunk_tables[chunk_idx][chunk_table_idx] = value;
    }
  }
  __syncthreads();
  if (tid >= (1u << group_size))
    return;
  pr acc = pr_one();
  unsigned consumed_bits = 0;
  for (unsigned chunk_idx = 0; chunk_idx < chunk_count; ++chunk_idx) {
    const unsigned remaining = group_size - consumed_bits;
    const unsigned chunk_size = remaining < GKR_EQ_CHUNK_SIZE ? remaining : GKR_EQ_CHUNK_SIZE;
    const unsigned shift = group_size - consumed_bits - chunk_size;
    const pr factor = chunk_tables[chunk_idx][(tid >> shift) & ((1u << chunk_size) - 1u)];
    acc = chunk_idx == 0 ? factor : pr::mul(acc, factor);
    consumed_bits += chunk_size;
  }
  destination[group_idx * GKR_EQ_GROUP_TABLE_LEN + tid] = acc;
}

DEVICE_FORCEINLINE void pr_dr_tail_finalize(pr c0, pr c1, const unsigned active_partials, const pr *prev_claim_coord, u8 *seed_io, pr *claim_io,
                                            pr *eq_prefactor_io, pr *coeffs_out, pr *challenge_out, pr *active_eq_slot_base,
                                            const unsigned active_eq_size_before_fold) {
  constexpr unsigned WARPS = PR_DR_TAIL_BLOCK_THREADS / 32;
  __shared__ pr warp_c0[WARPS];
  __shared__ pr warp_c1[WARPS];
  __shared__ pr inverses[2];
  const unsigned tid = threadIdx.x;
  const unsigned lane = tid & 31;
  const unsigned warp = tid >> 5;
  const unsigned partial_warps = (active_partials + 31) / 32;
  const unsigned active_warps = partial_warps < WARPS ? partial_warps : WARPS;
  if (warp < active_warps) {
    c0 = gkr_trace_holder_partials_warp_reduce_sum(c0);
    c1 = gkr_trace_holder_partials_warp_reduce_sum(c1);
    if (lane == 0) {
      warp_c0[warp] = c0;
      warp_c1[warp] = c1;
    }
  }
  __syncthreads();
  if (warp == 0) {
    c0 = gkr_trace_holder_partials_warp_reduce_sum(lane < active_warps ? warp_c0[lane] : pr_zero());
    c1 = gkr_trace_holder_partials_warp_reduce_sum(lane < active_warps ? warp_c1[lane] : pr_zero());
    if (lane < 2)
      inverses[lane] = pr::inv(lane == 0 ? *eq_prefactor_io : *prev_claim_coord);
    __syncwarp();
    if (lane == 0) {
      const pr prev_coord = *prev_claim_coord;
      *challenge_out = run_round_update_with_inverses_pr(c0, c1, prev_coord, inverses[0], inverses[1], seed_io, claim_io, eq_prefactor_io, coeffs_out);
    }
  }
  fold_active_eq_slot_pr<PR_DR_TAIL_BLOCK_THREADS>(active_eq_slot_base, active_eq_size_before_fold);
}

DEVICE_FORCEINLINE void pr_dr_tail_inner(const pr_dr_tail_megakernel_desc &desc, pr *global_state) {
  extern __shared__ __align__(32) unsigned char pr_dr_tail_dynamic_smem[];
  pr *state = global_state;

  const unsigned tid = threadIdx.x;
  const unsigned remaining_rounds = desc.folding_steps - desc.entry_round;
  const unsigned entry_rows = 1u << remaining_rounds;
  const unsigned source_stride = entry_rows * GKR_DIM_REDUCING_PAIR_STRIDE;
  pr *next_state = state + static_cast<size_t>(desc.source_count) * source_stride;
  pr *const eq_groups = reinterpret_cast<pr *>(pr_dr_tail_dynamic_smem);
  const unsigned eq_challenge_count = remaining_rounds - 1;
  const unsigned eq_group_count = gkr_eq_group_count(eq_challenge_count);

  __shared__ pr entry_weights[1u << PR_DR_TAIL_ENTRY_CHALLENGES];
  __shared__ pr entry_challenges[PR_DR_TAIL_ENTRY_CHALLENGES];
  __shared__ pr round_challenge;
  __shared__ gkr_eq_sizes eq_sizes_shared;
  const bool direct_entry = desc.entry_round == 0;
  if (tid < PR_DR_TAIL_ENTRY_CHALLENGES && !direct_entry)
    entry_challenges[tid] = load<pr, ld_modifier::cs>(desc.challenges_out, desc.entry_round - PR_DR_TAIL_ENTRY_CHALLENGES + tid);
  __syncthreads();
  if (tid < 8 && !direct_entry) {
    pr weight = pr_one();
#pragma unroll
    for (unsigned bit = 0; bit < PR_DR_TAIL_ENTRY_CHALLENGES; ++bit) {
      const pr factor = ((tid >> bit) & 1u) != 0 ? entry_challenges[bit] : pr::sub(pr_one(), entry_challenges[bit]);
      weight = pr::mul(weight, factor);
    }
    entry_weights[tid] = weight;
  }
  __syncthreads();

  for (unsigned source_idx = 0; source_idx < desc.source_count; ++source_idx) {
    const auto *source = reinterpret_cast<const pr_dr_tail_pair *>(desc.source_ptrs[source_idx]);
    auto *destination = reinterpret_cast<pr_dr_tail_pair *>(state + static_cast<size_t>(source_idx) * source_stride);
    if (direct_entry) {
      for (unsigned row = tid; row < entry_rows; row += PR_DR_TAIL_BLOCK_THREADS)
        destination[row] = load<pr_dr_tail_pair, ld_modifier::cs>(source, row);
    } else {
      const unsigned ancestor = tid & 7;
      for (unsigned base = 0; base < entry_rows; base += PR_DR_TAIL_BLOCK_THREADS / 8) {
        const unsigned row = base + tid / 8;
        pr_dr_tail_pair folded{{pr_zero(), pr_zero()}};
        if (row < entry_rows) {
          const auto value = load<pr_dr_tail_pair, ld_modifier::cs>(source, (row << 3) + ancestor);
          folded.cells[0] = pr::mul(entry_weights[ancestor], value.cells[0]);
          folded.cells[1] = pr::mul(entry_weights[ancestor], value.cells[1]);
        }
#pragma unroll
        for (unsigned offset = 4; offset != 0; offset >>= 1) {
#pragma unroll
          for (unsigned cell = 0; cell < 2; ++cell)
            folded.cells[cell] = pr::add(folded.cells[cell], shfl_xor(0xffffffffu, folded.cells[cell], offset, 8));
        }
        if (ancestor == 0 && row < entry_rows)
          destination[row] = folded;
      }
    }
  }
  __syncthreads();

  for (unsigned group = 0; group < eq_group_count; ++group) {
    pr_dr_tail_build_eq_group(desc.tau, desc.entry_round + 1, eq_challenge_count, group, eq_groups);
    __syncthreads();
  }
  if (tid == 0) {
    eq_sizes_shared.high[0] = 0;
    eq_sizes_shared.high[1] = 0;
    eq_sizes_shared.low = 0;
    unsigned consumed = 0;
    unsigned high_idx = 0;
    for (unsigned group = 0; group < eq_group_count; ++group) {
      const unsigned remaining = eq_challenge_count - consumed;
      const unsigned group_size = remaining < GKR_EQ_GROUP_SIZE ? remaining : GKR_EQ_GROUP_SIZE;
      if (group + 1 == eq_group_count)
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
    pr thread_partial0 = pr_zero();
    pr thread_partial1 = pr_zero();
    const pr_dr_tail_shared_eq_reader eq_reader{eq_groups, eq_sizes, eq_group_count};
    for (unsigned row = tid; row < acc_size; row += PR_DR_TAIL_BLOCK_THREADS) {
      pr row_partial0 = pr_zero();
      pr row_partial1 = pr_zero();
#pragma unroll 1
      for (unsigned slot_idx = 0; slot_idx < GKR_DIM_REDUCING_SLOTS; ++slot_idx) {
        if ((desc.enabled_mask & (1u << slot_idx)) == 0)
          continue;
        const pr_dr_tail_slot &slot = desc.slots[slot_idx];
        if (((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK >> slot_idx) & 1u) != 0)
          pr_dr_tail_evaluate_pairwise(state, source_stride, slot, desc.batch_challenges, row, row_partial0, row_partial1);
        else
          pr_dr_tail_evaluate_lookup(state, source_stride, slot, desc.batch_challenges, row, row_partial0, row_partial1);
      }
      const pr eq = eq_reader(row);
      thread_partial0 = pr::fma(eq, row_partial0, thread_partial0);
      thread_partial1 = pr::fma(eq, row_partial1, thread_partial1);
    }

    const bool final_round = round + 1 == desc.folding_steps;
    unsigned active_eq_size = 0;
    pr *const active_eq_slot = final_round ? eq_groups : pr_dr_tail_active_eq_slot(eq_groups, eq_group_count, eq_sizes, active_eq_size);
    pr_dr_tail_finalize(thread_partial0, thread_partial1, acc_size, desc.tau + round, desc.seed, desc.claim, desc.eq_prefactor, desc.coeffs_out + 4 * round,
                        &round_challenge, active_eq_slot, active_eq_size);
    __syncthreads();

    if (tid == 0)
      desc.challenges_out[round] = round_challenge;
    __syncthreads();

    if (!final_round) {
      if (tid == 0)
        pr_dr_tail_record_eq_fold(eq_sizes);
      __syncthreads();
      const unsigned next_cells = current_cells / 2;
      for (unsigned index = tid; index < desc.source_count * next_cells; index += PR_DR_TAIL_BLOCK_THREADS) {
        const unsigned source_idx = index / next_cells;
        const unsigned cell = index % next_cells;
        const pr *const source = state + static_cast<size_t>(source_idx) * source_stride;
        const unsigned ancestor = gkr_dim_reducing_ancestor_index(cell);
        const pr f0 = source[ancestor];
        const pr f1 = source[ancestor + GKR_DIM_REDUCING_PAIR_STRIDE];
        next_state[static_cast<size_t>(source_idx) * source_stride + cell] = pr::fma(round_challenge, pr::sub(f1, f0), f0);
      }
      __syncthreads();
      pr *const previous = state;
      state = next_state;
      next_state = previous;
      current_cells = next_cells;
    }
  }

  for (unsigned cell = tid; cell < desc.source_count * 4; cell += PR_DR_TAIL_BLOCK_THREADS) {
    const unsigned source_idx = cell / 4;
    const unsigned source_cell = cell % 4;
    store<pr, st_modifier::cs>(desc.final_sources, state[static_cast<size_t>(source_idx) * source_stride + source_cell], cell);
  }
}

} // namespace airbender::gkr::proth120::backward
