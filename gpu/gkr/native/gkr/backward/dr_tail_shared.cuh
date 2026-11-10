#pragma once

#include "../support/lookup_helpers.cuh"

namespace airbender::gkr::dr_tail_detail {

template <class F> struct shared_eq_reader {
  const F *groups;
  gkr_eq_sizes sizes;
  unsigned group_count;

  DEVICE_FORCEINLINE F operator()(const unsigned row) const {
    F result = F::ONE();
    if (sizes.high[0] != 0) {
      const unsigned shift = sizes.high[1] + sizes.low;
      const unsigned index = (row >> shift) & ((1u << sizes.high[0]) - 1u);
      result = F::mul(result, groups[index]);
    }
    if (sizes.high[1] != 0) {
      const unsigned index = (row >> sizes.low) & ((1u << sizes.high[1]) - 1u);
      result = F::mul(result, groups[GKR_EQ_GROUP_TABLE_LEN + index]);
    }
    if (sizes.low != 0) {
      const unsigned index = row & ((1u << sizes.low) - 1u);
      result = F::mul(result, groups[(group_count - 1) * GKR_EQ_GROUP_TABLE_LEN + index]);
    }
    return result;
  }
};

template <class F> DEVICE_FORCEINLINE F *resolve_active_eq_slot(F *groups, const unsigned group_count, const gkr_eq_sizes &sizes, unsigned &size) {
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

DEVICE_FORCEINLINE void record_eq_fold(gkr_eq_sizes &sizes) {
  if (sizes.low != 0)
    --sizes.low;
  else if (sizes.high[1] != 0)
    --sizes.high[1];
  else
    --sizes.high[0];
}

template <class Policy, class F = typename Policy::Field, class Slot = typename Policy::Slot>
DEVICE_FORCEINLINE void evaluate_pairwise(const typename Policy::Desc &desc, const F *state, const unsigned source_stride, const Slot &slot, const unsigned row,
                                          F &partial0, F &partial1) {
  const unsigned cell = GKR_DIM_REDUCING_ROW_SPAN * row;
#pragma unroll
  for (unsigned input = 0; input < GKR_DIM_REDUCING_INPUTS_PER_SLOT; ++input) {
    const F *source = state + static_cast<size_t>(slot.input_source[input]) * source_stride;
    const F even0 = source[cell];
    const F odd0 = source[cell + 1];
    const F even_delta = F::sub(source[cell + GKR_DIM_REDUCING_PAIR_STRIDE], even0);
    const F odd_delta = F::sub(source[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], odd0);
    const F batch_challenge = Policy::batch(desc, slot.batch_exp[input]);
    F value0;
    F value1;
    gkr_eval_product(even0, odd0, value0);
    gkr_eval_product(even_delta, odd_delta, value1);
    partial0 = F::fma(batch_challenge, value0, partial0);
    partial1 = F::fma(batch_challenge, value1, partial1);
  }
}

template <class Policy, class F = typename Policy::Field, class Slot = typename Policy::Slot>
DEVICE_FORCEINLINE void evaluate_lookup(const typename Policy::Desc &desc, const F *state, const unsigned source_stride, const Slot &slot, const unsigned row,
                                        F &partial0, F &partial1) {
  const unsigned cell = GKR_DIM_REDUCING_ROW_SPAN * row;
  const F *a = state + static_cast<size_t>(slot.input_source[0]) * source_stride;
  const F *b = state + static_cast<size_t>(slot.input_source[1]) * source_stride;
  const F a0 = a[cell];
  const F b0 = b[cell];
  const F c0 = a[cell + 1];
  const F d0 = b[cell + 1];
  const F a1 = F::sub(a[cell + GKR_DIM_REDUCING_PAIR_STRIDE], a0);
  const F b1 = F::sub(b[cell + GKR_DIM_REDUCING_PAIR_STRIDE], b0);
  const F c1 = F::sub(a[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], c0);
  const F d1 = F::sub(b[cell + GKR_DIM_REDUCING_PAIR_STRIDE + 1], d0);
  F num0;
  F den0;
  F num1;
  F den1;
  gkr_eval_lookup_pair(a0, b0, c0, d0, num0, den0);
  gkr_eval_lookup_pair(a1, b1, c1, d1, num1, den1);
  const F batch0 = Policy::batch(desc, slot.batch_exp[0]);
  const F batch1 = Policy::batch(desc, slot.batch_exp[1]);
  partial0 = F::fma(batch0, num0, F::fma(batch1, den0, partial0));
  partial1 = F::fma(batch0, num1, F::fma(batch1, den1, partial1));
}

template <class Policy, class F = typename Policy::Field>
DEVICE_FORCEINLINE void finalize(F c0, F c1, const unsigned active_partials, const F *prev_claim_coord, typename Policy::SeedWord *seed_io, F *claim_io,
                                 F *eq_prefactor_io, F *coeffs_out, F *challenge_out, F *active_eq_slot_base, const unsigned active_eq_size_before_fold) {
  constexpr unsigned WARPS = Policy::THREADS / 32;
  __shared__ F warp_c0[WARPS];
  __shared__ F warp_c1[WARPS];
  __shared__ F inverses[2];
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
    c0 = gkr_trace_holder_partials_warp_reduce_sum(lane < active_warps ? warp_c0[lane] : F::ZERO());
    c1 = gkr_trace_holder_partials_warp_reduce_sum(lane < active_warps ? warp_c1[lane] : F::ZERO());
    if (lane < 2)
      inverses[lane] = F::inv(lane == 0 ? *eq_prefactor_io : *prev_claim_coord);
    __syncwarp();
    if (lane == 0) {
      const F prev_coord = *prev_claim_coord;
      *challenge_out = Policy::round_update(c0, c1, prev_coord, inverses[0], inverses[1], seed_io, claim_io, eq_prefactor_io, coeffs_out);
    }
  }
  Policy::fold_eq(active_eq_slot_base, active_eq_size_before_fold);
}

template <class Policy> DEVICE_FORCEINLINE void inner(const typename Policy::Desc &desc, typename Policy::Field *global_state) {
  using F = typename Policy::Field;
  using Pair = typename Policy::Pair;
  using Slot = typename Policy::Slot;
  extern __shared__ __align__(32) unsigned char dynamic_smem[];
  F *state = global_state;

  const unsigned tid = threadIdx.x;
  const unsigned remaining_rounds = desc.folding_steps - desc.entry_round;
  const unsigned entry_rows = 1u << remaining_rounds;
  const unsigned source_stride = entry_rows * GKR_DIM_REDUCING_PAIR_STRIDE;
  F *next_state = state + static_cast<size_t>(desc.source_count) * source_stride;
  F *const eq_groups = reinterpret_cast<F *>(dynamic_smem);
  const unsigned eq_challenge_count = remaining_rounds - 1;
  const unsigned eq_group_count = gkr_eq_group_count(eq_challenge_count);

  __shared__ F entry_weights[1u << Policy::ENTRY_CHALLENGES];
  // Keep the entry challenge tuple in shared memory. A thread-0 local array
  // becomes a 16-byte local-memory spill in the linked production kernel,
  // which is forbidden by the resource admission gate.
  __shared__ F entry_challenges[Policy::ENTRY_CHALLENGES];
  __shared__ F round_challenge;
  __shared__ gkr_eq_sizes eq_sizes_shared;
  // Entry 0 starts from raw canonical pairs: no challenges have been drawn, so
  // the loader copies instead of folding.
  const bool direct_entry = desc.entry_round == 0;
  if (tid < Policy::ENTRY_CHALLENGES && !direct_entry)
    entry_challenges[tid] = load<F, ld_modifier::cs>(desc.challenges_out, desc.entry_round - Policy::ENTRY_CHALLENGES + tid);
  __syncthreads();
  if (tid < 8 && !direct_entry) {
    F weight = F::ONE();
#pragma unroll
    for (unsigned bit = 0; bit < Policy::ENTRY_CHALLENGES; ++bit) {
      const F factor = ((tid >> bit) & 1u) != 0 ? entry_challenges[bit] : F::sub(F::ONE(), entry_challenges[bit]);
      weight = F::mul(weight, factor);
    }
    entry_weights[tid] = weight;
  }
  __syncthreads();

  for (unsigned source_idx = 0; source_idx < desc.source_count; ++source_idx) {
    const auto *source = reinterpret_cast<const Pair *>(desc.source_ptrs[source_idx]);
    auto *destination = reinterpret_cast<Pair *>(state + static_cast<size_t>(source_idx) * source_stride);
    if (direct_entry) {
      for (unsigned row = tid; row < entry_rows; row += Policy::THREADS)
        destination[row] = load<Pair, ld_modifier::cs>(source, row);
    } else {
      const unsigned ancestor = tid & 7;
      // Eight adjacent lanes read eight adjacent canonical ancestor pairs.
      for (unsigned base = 0; base < entry_rows; base += Policy::THREADS / 8) {
        const unsigned row = base + tid / 8;
        Pair folded{{F::ZERO(), F::ZERO()}};
        if (row < entry_rows) {
          const auto value = load<Pair, ld_modifier::cs>(source, (row << 3) + ancestor);
          folded.cells[0] = F::mul(entry_weights[ancestor], value.cells[0]);
          folded.cells[1] = F::mul(entry_weights[ancestor], value.cells[1]);
        }
#pragma unroll
        for (unsigned offset = 4; offset != 0; offset >>= 1) {
#pragma unroll
          for (unsigned cell = 0; cell < 2; ++cell) {
            const F other = Policy::shuffle_value(folded.cells[cell], offset);
            folded.cells[cell] = F::add(folded.cells[cell], other);
          }
        }
        if (ancestor == 0 && row < entry_rows)
          destination[row] = folded;
      }
    }
  }
  __syncthreads();

  // Rebuild exactly Eq(tau[entry_round + 1 .. folding_steps]) in shared memory.
  for (unsigned group = 0; group < eq_group_count; ++group) {
    Policy::build_eq_group(desc.tau, desc.entry_round + 1, eq_challenge_count, group, eq_groups);
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
    F thread_partial0 = F::ZERO();
    F thread_partial1 = F::ZERO();
    const shared_eq_reader<F> eq_reader{eq_groups, eq_sizes, eq_group_count};
    for (unsigned row = tid; row < acc_size; row += Policy::THREADS) {
      F row_partial0 = F::ZERO();
      F row_partial1 = F::ZERO();
#pragma unroll 1
      for (unsigned slot_idx = 0; slot_idx < GKR_DIM_REDUCING_SLOTS; ++slot_idx) {
        if ((desc.enabled_mask & (1u << slot_idx)) == 0)
          continue;
        const Slot &slot = desc.slots[slot_idx];
        if (((GKR_DIM_REDUCING_PAIRWISE_SLOT_MASK >> slot_idx) & 1u) != 0)
          evaluate_pairwise<Policy>(desc, state, source_stride, slot, row, row_partial0, row_partial1);
        else
          evaluate_lookup<Policy>(desc, state, source_stride, slot, row, row_partial0, row_partial1);
      }
      const F eq = eq_reader(row);
      thread_partial0 = F::fma(eq, row_partial0, thread_partial0);
      thread_partial1 = F::fma(eq, row_partial1, thread_partial1);
    }

    const bool final_round = round + 1 == desc.folding_steps;
    unsigned active_eq_size = 0;
    F *const active_eq_slot = final_round ? eq_groups : resolve_active_eq_slot(eq_groups, eq_group_count, eq_sizes, active_eq_size);
    finalize<Policy>(thread_partial0, thread_partial1, acc_size, desc.tau + round, desc.seed, desc.claim, desc.eq_prefactor, desc.coeffs_out + 4 * round,
                     &round_challenge, active_eq_slot, active_eq_size);
    __syncthreads();

    // The finalizer reads tau[round] before publishing this challenge.
    if (tid == 0)
      desc.challenges_out[round] = round_challenge;
    __syncthreads();

    if (!final_round) {
      // The finalizer folded exactly one slot; mirror the same low > high[1] > high[0] transition.
      if (tid == 0)
        record_eq_fold(eq_sizes);
      __syncthreads();
      const unsigned next_cells = current_cells / 2;
      // Each output goes to the other buffer; readers never overlap writers.
      for (unsigned index = tid; index < desc.source_count * next_cells; index += Policy::THREADS) {
        const unsigned source_idx = index / next_cells;
        const unsigned cell = index % next_cells;
        const F *const source = state + static_cast<size_t>(source_idx) * source_stride;
        const unsigned ancestor = gkr_dim_reducing_ancestor_index(cell);
        const F f0 = source[ancestor];
        const F f1 = source[ancestor + GKR_DIM_REDUCING_PAIR_STRIDE];
        next_state[static_cast<size_t>(source_idx) * source_stride + cell] = F::fma(round_challenge, F::sub(f1, f0), f0);
      }
      __syncthreads();
      F *const previous = state;
      state = next_state;
      next_state = previous;
      current_cells = next_cells;
    }
  }

  // The epilogue publishes four pre-LSB cells per canonical source.
  for (unsigned cell = tid; cell < desc.source_count * 4; cell += Policy::THREADS) {
    const unsigned source_idx = cell / 4;
    const unsigned source_cell = cell % 4;
    store<F, st_modifier::cs>(desc.final_sources, state[static_cast<size_t>(source_idx) * source_stride + source_cell], cell);
  }
}

} // namespace airbender::gkr::dr_tail_detail
