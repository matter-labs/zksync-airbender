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
static_assert(2 * GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE == GKR_DR_TAIL_BLOCK_THREADS,
              "DR-tail first contraction must assign at most one destination per thread");

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
static_assert(sizeof(gkr_dr_tail_megakernel_desc) <= 32764, "DR-tail kernel parameters exceed CUDA limit");

struct __align__(32) gkr_dr_tail_e4_pair {
  e4 cells[2];
};

static_assert(sizeof(gkr_dr_tail_e4_pair) == 32 && alignof(gkr_dr_tail_e4_pair) == 32, "DR-tail packed E4 pair ABI drift");

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

// The full continuation accumulators resolve and fold global-memory source
// descriptors. This tail already owns the folded values in shared memory, so
// it reuses the shared scalar relation helpers and keeps only the shared indexing
// and batch accumulation local.
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

struct gkr_dr_tail_register_partial {
  e4 value0;
  e4 value1;

  DEVICE_FORCEINLINE void operator()(const unsigned, e4 &partial0, e4 &partial1) const {
    partial0 = value0;
    partial1 = value1;
  }
};

struct gkr_dr_tail_noop_recorder {
  static constexpr bool ENABLED = false;

  DEVICE_FORCEINLINE void record_entry(const gkr_dr_tail_megakernel_desc &, const e4 *, const unsigned, const e4 *, const gkr_eq_sizes, const unsigned) const {}
  DEVICE_FORCEINLINE void record_round(const gkr_dr_tail_megakernel_desc &, const unsigned, const e4 *, const unsigned, const unsigned, const e4 *,
                                       const gkr_eq_sizes, const unsigned) const {}
  DEVICE_FORCEINLINE void record_final(const gkr_dr_tail_megakernel_desc &, const e4 *, const unsigned) const {}
};

// Test-only recorder ABI. The production wrapper never instantiates this
// policy; the feature-gated diagnostic TU supplies it to the same recursive
// inner used above. Snapshot strides are fixed at the admitted maxima so the
// host can validate every shared-memory index without duplicating device
// layout arithmetic.
struct gkr_dr_tail_trace_desc {
  e4 *eq_groups;
  e4 *eq_rows;
  e4 *entry_levels;
  e4 *source_levels;
  e4 *transcript;
  e4 *final_cells;
  u32 *seeds;
  u32 *metadata;
};

static_assert(alignof(gkr_dr_tail_trace_desc) == 8 && sizeof(gkr_dr_tail_trace_desc) == 64, "DR-tail trace descriptor ABI drift");
static_assert(__builtin_offsetof(gkr_dr_tail_trace_desc, eq_groups) == 0 && __builtin_offsetof(gkr_dr_tail_trace_desc, eq_rows) == 8 &&
                  __builtin_offsetof(gkr_dr_tail_trace_desc, entry_levels) == 16 && __builtin_offsetof(gkr_dr_tail_trace_desc, source_levels) == 24 &&
                  __builtin_offsetof(gkr_dr_tail_trace_desc, transcript) == 32 && __builtin_offsetof(gkr_dr_tail_trace_desc, final_cells) == 40 &&
                  __builtin_offsetof(gkr_dr_tail_trace_desc, seeds) == 48 && __builtin_offsetof(gkr_dr_tail_trace_desc, metadata) == 56,
              "DR-tail trace descriptor offsets drift");
static_assert(sizeof(gkr_dr_tail_megakernel_desc) + sizeof(gkr_dr_tail_trace_desc) <= 32764, "DR-tail trace kernel parameters exceed CUDA limit");

struct gkr_dr_tail_global_recorder {
  static constexpr bool ENABLED = true;
  static constexpr unsigned EQ_GROUP_STRIDE = 2 * GKR_EQ_GROUP_TABLE_LEN;
  static constexpr unsigned EQ_ROW_STRIDE = GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE;
  static constexpr unsigned ENTRY_SOURCE_STRIDE = GKR_DR_TAIL_MAX_SOURCES * 16 * GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE;
  static constexpr unsigned SOURCE_STRIDE = GKR_DR_TAIL_MAX_SOURCES * 4 * GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE;
  static constexpr unsigned TRANSCRIPT_STRIDE = 3;
  static constexpr unsigned METADATA_STRIDE = 8;

  static_assert(SOURCE_STRIDE == 5120, "DR-tail trace source snapshot stride drift");
  static_assert(ENTRY_SOURCE_STRIDE == 20480, "DR-tail trace entry snapshot stride drift");

  gkr_dr_tail_trace_desc trace;

  DEVICE_FORCEINLINE void record_snapshot(const gkr_dr_tail_megakernel_desc &desc, const unsigned snapshot, const e4 *state, const unsigned source_stride,
                                          const unsigned current_cells, const e4 *eq_groups, const gkr_eq_sizes sizes, const unsigned group_count) const {
    const unsigned tid = threadIdx.x;
    const unsigned represented_bits = sizes.high[0] + sizes.high[1] + sizes.low;
    const unsigned represented_rows = 1u << represented_bits;
    const gkr_dr_tail_shared_eq_reader eq_reader{eq_groups, sizes, group_count};
    for (unsigned cell = tid; cell < desc.source_count * current_cells; cell += GKR_DR_TAIL_BLOCK_THREADS) {
      const unsigned source = cell / current_cells;
      const unsigned source_cell = cell % current_cells;
      trace.source_levels[static_cast<size_t>(snapshot) * SOURCE_STRIDE + static_cast<size_t>(source) * source_stride + source_cell] =
          state[static_cast<size_t>(source) * source_stride + source_cell];
    }
    for (unsigned cell = tid; cell < group_count * GKR_EQ_GROUP_TABLE_LEN; cell += GKR_DR_TAIL_BLOCK_THREADS)
      trace.eq_groups[static_cast<size_t>(snapshot) * EQ_GROUP_STRIDE + cell] = eq_groups[cell];
    for (unsigned row = tid; row < represented_rows; row += GKR_DR_TAIL_BLOCK_THREADS)
      trace.eq_rows[static_cast<size_t>(snapshot) * EQ_ROW_STRIDE + row] = eq_reader(row);
    if (tid == 0) {
      u32 *const metadata = trace.metadata + static_cast<size_t>(snapshot) * METADATA_STRIDE;
      metadata[0] = sizes.high[0];
      metadata[1] = sizes.high[1];
      metadata[2] = sizes.low;
      metadata[3] = represented_rows;
      metadata[4] = current_cells;
      metadata[5] = group_count;
      metadata[6] = source_stride;
      metadata[7] = desc.source_count * source_stride;
    }
  }

  DEVICE_FORCEINLINE void record_entry(const gkr_dr_tail_megakernel_desc &desc, const e4 *state, const unsigned source_stride, const e4 *eq_groups,
                                       const gkr_eq_sizes sizes, const unsigned group_count) const {
    const unsigned first_level_cells = 4 * source_stride;
    const unsigned second_level_cells = 2 * source_stride;
    const e4 entry_challenge0 = desc.challenges_out[desc.entry_round - 3];
    const e4 entry_challenge1 = desc.challenges_out[desc.entry_round - 2];
    const e4 entry_challenge2 = desc.challenges_out[desc.entry_round - 1];
    for (unsigned cell = threadIdx.x; cell < desc.source_count * first_level_cells; cell += GKR_DR_TAIL_BLOCK_THREADS) {
      const unsigned source = cell / first_level_cells;
      const unsigned destination = cell % first_level_cells;
      const unsigned ancestor = gkr_dim_reducing_ancestor_index(destination);
      const e4 *const input = desc.source_ptrs[source];
      const e4 f0 = input[ancestor];
      const e4 f1 = input[ancestor + GKR_DIM_REDUCING_PAIR_STRIDE];
      trace.entry_levels[static_cast<size_t>(source) * first_level_cells + destination] = e4::fma(entry_challenge0, e4::sub(f1, f0), f0);
    }
    __syncthreads();
    for (unsigned cell = threadIdx.x; cell < desc.source_count * second_level_cells; cell += GKR_DR_TAIL_BLOCK_THREADS) {
      const unsigned source = cell / second_level_cells;
      const unsigned destination = cell % second_level_cells;
      const unsigned ancestor = gkr_dim_reducing_ancestor_index(destination);
      const e4 *const input = trace.entry_levels + static_cast<size_t>(source) * first_level_cells;
      const e4 f0 = input[ancestor];
      const e4 f1 = input[ancestor + GKR_DIM_REDUCING_PAIR_STRIDE];
      trace.entry_levels[ENTRY_SOURCE_STRIDE + static_cast<size_t>(source) * first_level_cells + destination] = e4::fma(entry_challenge1, e4::sub(f1, f0), f0);
    }
    __syncthreads();
    for (unsigned cell = threadIdx.x; cell < desc.source_count * source_stride; cell += GKR_DR_TAIL_BLOCK_THREADS) {
      const unsigned source = cell / source_stride;
      const unsigned destination = cell % source_stride;
      const unsigned ancestor = gkr_dim_reducing_ancestor_index(destination);
      const e4 *const input = trace.entry_levels + ENTRY_SOURCE_STRIDE + static_cast<size_t>(source) * first_level_cells;
      const e4 f0 = input[ancestor];
      const e4 f1 = input[ancestor + GKR_DIM_REDUCING_PAIR_STRIDE];
      trace.entry_levels[2 * ENTRY_SOURCE_STRIDE + static_cast<size_t>(source) * first_level_cells + destination] =
          e4::fma(entry_challenge2, e4::sub(f1, f0), f0);
    }
    __syncthreads();
    record_snapshot(desc, 0, state, source_stride, source_stride, eq_groups, sizes, group_count);
  }

  DEVICE_FORCEINLINE void record_round(const gkr_dr_tail_megakernel_desc &desc, const unsigned round, const e4 *state, const unsigned source_stride,
                                       const unsigned current_cells, const e4 *eq_groups, const gkr_eq_sizes sizes, const unsigned group_count) const {
    const unsigned round_index = round - desc.entry_round;
    if (threadIdx.x == 0) {
      e4 *const transcript = trace.transcript + static_cast<size_t>(round_index) * TRANSCRIPT_STRIDE;
      transcript[0] = desc.challenges_out[round];
      transcript[1] = *desc.claim;
      transcript[2] = *desc.eq_prefactor;
    }
    if (threadIdx.x < 8)
      trace.seeds[static_cast<size_t>(round_index) * 8 + threadIdx.x] = desc.seed[threadIdx.x];
    if (round + 1 < desc.folding_steps)
      record_snapshot(desc, round_index + 1, state, source_stride, current_cells, eq_groups, sizes, group_count);
  }

  DEVICE_FORCEINLINE void record_final(const gkr_dr_tail_megakernel_desc &desc, const e4 *state, const unsigned source_stride) const {
    for (unsigned cell = threadIdx.x; cell < desc.source_count * 4; cell += GKR_DR_TAIL_BLOCK_THREADS) {
      const unsigned source = cell / 4;
      const unsigned source_cell = cell % 4;
      trace.final_cells[cell] = state[static_cast<size_t>(source) * source_stride + source_cell];
    }
  }
};

template <typename Recorder> DEVICE_FORCEINLINE void gkr_dr_tail_megakernel_inner(const gkr_dr_tail_megakernel_desc &desc, const Recorder &recorder) {
  extern __shared__ __align__(32) unsigned char dynamic_smem[];
  e4 *const state = reinterpret_cast<e4 *>(dynamic_smem);

  const unsigned tid = threadIdx.x;
  const unsigned remaining_rounds = desc.folding_steps - desc.entry_round;
  const unsigned entry_rows = 1u << remaining_rounds;
  const unsigned source_stride = entry_rows * GKR_DIM_REDUCING_PAIR_STRIDE;
  e4 *const eq_groups = state + static_cast<size_t>(desc.source_count) * source_stride;
  const unsigned eq_challenge_count = remaining_rounds - 1;
  const unsigned eq_group_count = gkr_eq_group_count(eq_challenge_count);

  __shared__ e4 entry_weights[1u << GKR_DR_TAIL_ENTRY_CHALLENGES];
  // Keep the entry challenge tuple in shared memory. A thread-0 local array
  // becomes a 16-byte local-memory spill in the linked production kernel,
  // which is forbidden by the resource admission gate.
  __shared__ e4 entry_challenges[GKR_DR_TAIL_ENTRY_CHALLENGES];
  __shared__ e4 round_challenge;
  __shared__ gkr_eq_sizes eq_sizes_shared;
  if (tid == 0) {
#pragma unroll
    for (unsigned bit = 0; bit < GKR_DR_TAIL_ENTRY_CHALLENGES; ++bit)
      entry_challenges[bit] = load<e4, ld_modifier::cs>(desc.challenges_out, desc.entry_round - GKR_DR_TAIL_ENTRY_CHALLENGES + bit);
#pragma unroll
    for (unsigned ancestor = 0; ancestor < (1u << GKR_DR_TAIL_ENTRY_CHALLENGES); ++ancestor) {
      e4 weight = e4::ONE();
#pragma unroll
      for (unsigned bit = 0; bit < GKR_DR_TAIL_ENTRY_CHALLENGES; ++bit) {
        const e4 factor = ((ancestor >> bit) & 1u) != 0 ? entry_challenges[bit] : e4::sub(e4::ONE(), entry_challenges[bit]);
        weight = e4::mul(weight, factor);
      }
      entry_weights[ancestor] = weight;
    }
  }
  __syncthreads();

  // Fold the three draw-order entry coordinates while retaining gate bit b.
  for (unsigned source_idx = 0; source_idx < desc.source_count; ++source_idx) {
    const gkr_dr_tail_e4_pair *const source = reinterpret_cast<const gkr_dr_tail_e4_pair *>(desc.source_ptrs[source_idx]);
    for (unsigned row = tid; row < entry_rows; row += GKR_DR_TAIL_BLOCK_THREADS) {
      gkr_dr_tail_e4_pair folded{{e4::ZERO(), e4::ZERO()}};
#pragma unroll
      for (unsigned ancestor = 0; ancestor < (1u << GKR_DR_TAIL_ENTRY_CHALLENGES); ++ancestor) {
        const gkr_dr_tail_e4_pair pair = load<gkr_dr_tail_e4_pair, ld_modifier::cs>(source, (row << GKR_DR_TAIL_ENTRY_CHALLENGES) + ancestor);
        folded.cells[0] = e4::fma(entry_weights[ancestor], pair.cells[0], folded.cells[0]);
        folded.cells[1] = e4::fma(entry_weights[ancestor], pair.cells[1], folded.cells[1]);
      }
      *reinterpret_cast<gkr_dr_tail_e4_pair *>(state + static_cast<size_t>(source_idx) * source_stride + row * GKR_DIM_REDUCING_PAIR_STRIDE) = folded;
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
  if constexpr (Recorder::ENABLED) {
    recorder.record_entry(desc, state, source_stride, eq_groups, eq_sizes, eq_group_count);
    __syncthreads();
  }

  unsigned current_cells = source_stride;
  for (unsigned round = desc.entry_round; round < desc.folding_steps; ++round) {
    const unsigned acc_size = current_cells / GKR_DIM_REDUCING_ROW_SPAN;
    e4 thread_partial0 = e4::ZERO();
    e4 thread_partial1 = e4::ZERO();
    const gkr_dr_tail_shared_eq_reader eq_reader{eq_groups, eq_sizes, eq_group_count};
    for (unsigned row = tid; row < acc_size; row += GKR_DR_TAIL_BLOCK_THREADS) {
      e4 row_partial0 = e4::ZERO();
      e4 row_partial1 = e4::ZERO();
#pragma unroll
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
    const gkr_dr_tail_register_partial partials{thread_partial0, thread_partial1};
    mega_finalize_block<GKR_DR_TAIL_BLOCK_THREADS>(partials, GKR_DR_TAIL_BLOCK_THREADS, desc.tau + round, desc.seed, desc.claim, desc.eq_prefactor,
                                                   desc.coeffs_out + 4 * round, &round_challenge, active_eq_slot, active_eq_size);
    __syncthreads();

    // `mega_finalize_block` loaded tau[round] before publishing this challenge.
    if (tid == 0)
      desc.challenges_out[round] = round_challenge;
    __syncthreads();

    if (!final_round) {
      // The finalizer folded exactly one slot; mirror the same low > high[1] > high[0] transition.
      gkr_dr_tail_record_eq_fold(eq_sizes);
      const unsigned next_cells = current_cells / 2;
      for (unsigned source_idx = 0; source_idx < desc.source_count; ++source_idx) {
        e4 folded = e4::ZERO();
        const bool active = tid < next_cells;
        if (active) {
          const e4 *const source = state + static_cast<size_t>(source_idx) * source_stride;
          const unsigned ancestor = gkr_dim_reducing_ancestor_index(tid);
          const e4 f0 = source[ancestor];
          const e4 f1 = source[ancestor + GKR_DIM_REDUCING_PAIR_STRIDE];
          folded = e4::fma(round_challenge, e4::sub(f1, f0), f0);
        }
        __syncthreads();
        if (active)
          state[static_cast<size_t>(source_idx) * source_stride + tid] = folded;
        __syncthreads();
      }
      current_cells = next_cells;
    }

    if constexpr (Recorder::ENABLED) {
      recorder.record_round(desc, round, state, source_stride, current_cells, eq_groups, eq_sizes, eq_group_count);
      __syncthreads();
    }
  }

  // The unchanged epilogue consumes four pre-LSB cells per canonical source.
  for (unsigned cell = tid; cell < desc.source_count * 4; cell += GKR_DR_TAIL_BLOCK_THREADS) {
    const unsigned source_idx = cell / 4;
    const unsigned source_cell = cell % 4;
    store<e4, st_modifier::cs>(desc.final_sources, state[static_cast<size_t>(source_idx) * source_stride + source_cell], cell);
  }
  if constexpr (Recorder::ENABLED) {
    __syncthreads();
    recorder.record_final(desc, state, source_stride);
    __syncthreads();
  }
}

} // namespace airbender::gkr::backward
