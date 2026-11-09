#pragma once

#include "../../backward/window/common.cuh"
#include "tail_common_pr.cuh"

namespace airbender::gkr::proth120::backward {

constexpr u32 BWD_PR_MAIN_TAIL_BLOCK_THREADS = 256;
constexpr u32 BWD_PR_MAIN_TAIL_K = 8;
constexpr u32 BWD_PR_MAIN_TAIL_LIST_OFFSETS = BWD_PR_MAIN_TAIL_K + 1;
constexpr u32 BWD_PR_MAIN_TAIL_LIST_OFFSETS_OFFSET = 0;
constexpr u32 BWD_PR_MAIN_TAIL_PROGRAM_OFFSET = 18;
constexpr u32 BWD_PR_MAIN_TAIL_PROGRAM_WORD_CAP = 8192;
constexpr u32 BWD_PR_MAIN_TAIL_BLOB_BYTES = 16416;
constexpr u32 BWD_PR_MAIN_TAIL_SOURCE_CAP = 1072;
constexpr u32 BWD_PR_MAIN_TAIL_IMMEDIATE_CAP = 512;
constexpr u32 BWD_PR_MAIN_TAIL_D3_WEIGHTS = 7;
constexpr u16 BWD_PR_MAIN_TAIL_C_INIT_NONE = 0xffff;

static_assert(BWD_PR_MAIN_TAIL_PROGRAM_OFFSET == BWD_PR_MAIN_TAIL_LIST_OFFSETS * sizeof(u16), "main-tail program offset drift");
static_assert(BWD_PR_MAIN_TAIL_BLOB_BYTES == ((BWD_PR_MAIN_TAIL_PROGRAM_OFFSET + BWD_PR_MAIN_TAIL_PROGRAM_WORD_CAP * sizeof(u16) + 15) / 16) * 16,
              "main-tail blob size drift");
static_assert(BWD_PR_MAIN_TAIL_SOURCE_CAP == BWD_CONTINUATION_MAX_SOURCES, "main-tail source capacity drift");

struct __align__(16) bwd_pr_main_tail_desc {
  const u8 *program_blob;
  const pr *entry;
  pr *ping;
  pr *pong;
  pr *eq_low;
  const pr *eq_high;
  const pr *prev_claim_coordinates;
  u8 *seed;
  pr *claim;
  pr *eq_prefactor;
  pr *coefficients_out;
  pr *challenges_out;
  const pr *coefficients;
  const pr *immediates;
  gkr_eq_sizes eq_sizes;
  u32 entry_column_elems;
  u16 source_count;
  u16 program_words;
  u16 immediate_count;
  u16 c_init_coeff_id;
  u8 tail_start;
  u8 folding_steps;
  u8 tail_padding[6];
};

struct __align__(16) bwd_pr_main_tail_program_blob {
  u8 bytes[BWD_PR_MAIN_TAIL_BLOB_BYTES];
};

static_assert(sizeof(bwd_pr_main_tail_desc) == 144, "pr main-tail descriptor size drift");
static_assert(alignof(bwd_pr_main_tail_desc) == 16, "pr main-tail descriptor alignment drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, program_blob) == 0, "program_blob ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, entry) == 8, "entry ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, ping) == 16, "ping ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, pong) == 24, "pong ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, eq_low) == 32, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, eq_high) == 40, "eq_high ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, prev_claim_coordinates) == 48, "prev_claim_coordinates ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, seed) == 56, "seed ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, claim) == 64, "claim ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, eq_prefactor) == 72, "eq_prefactor ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, coefficients_out) == 80, "coefficients_out ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, challenges_out) == 88, "challenges_out ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, coefficients) == 96, "coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, immediates) == 104, "immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, eq_sizes) == 112, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, entry_column_elems) == 124, "entry_column_elems ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, source_count) == 128, "source_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, program_words) == 130, "program_words ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, immediate_count) == 132, "immediate_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, c_init_coeff_id) == 134, "c_init_coeff_id ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, tail_start) == 136, "tail_start ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, folding_steps) == 137, "folding_steps ABI offset drift");
static_assert(__builtin_offsetof(bwd_pr_main_tail_desc, tail_padding) == 138, "tail_padding ABI offset drift");
static_assert(sizeof(bwd_pr_main_tail_program_blob) == BWD_PR_MAIN_TAIL_BLOB_BYTES, "pr main-tail program blob size drift");
static_assert(alignof(bwd_pr_main_tail_program_blob) == 16, "pr main-tail program blob alignment drift");
static_assert(sizeof(bwd_pr_main_tail_desc) + sizeof(bwd_pr_main_tail_program_blob) == 16560, "pr main-tail argument size drift");

DEVICE_FORCEINLINE const u16 *bwd_pr_main_tail_list_offsets(const u8 *program_blob) {
  return reinterpret_cast<const u16 *>(program_blob + BWD_PR_MAIN_TAIL_LIST_OFFSETS_OFFSET);
}

DEVICE_FORCEINLINE const u16 *bwd_pr_main_tail_program(const u8 *program_blob) {
  return reinterpret_cast<const u16 *>(program_blob + BWD_PR_MAIN_TAIL_PROGRAM_OFFSET);
}

DEVICE_FORCEINLINE pr bwd_pr_main_tail_eq_weight(const bool bit, const pr coordinate) { return bit ? coordinate : pr::sub(pr::ONE(), coordinate); }

DEVICE_FORCEINLINE void bwd_pr_main_tail_build_d3_weights(const bwd_pr_main_tail_desc &desc, pr (&weights)[BWD_PR_MAIN_TAIL_D3_WEIGHTS]) {
  if (threadIdx.x < BWD_PR_MAIN_TAIL_D3_WEIGHTS) {
    const u32 q = threadIdx.x + 1;
    pr weight = pr::ONE();
#pragma unroll
    for (u32 bit = 0; bit < 3; ++bit) {
      const pr coordinate = desc.challenges_out[u32{desc.tail_start} - 3u + bit];
      weight = pr::mul(weight, bwd_pr_main_tail_eq_weight(((q >> bit) & 1u) != 0, coordinate));
    }
    weights[threadIdx.x] = weight;
  }
}

DEVICE_FORCEINLINE void bwd_pr_main_tail_fold_d3(const bwd_pr_main_tail_desc &desc, const u32 output_stride, const pr (&weights)[BWD_PR_MAIN_TAIL_D3_WEIGHTS]) {
  const u32 total = u32{desc.source_count} * output_stride;
  for (u32 flat = threadIdx.x; flat < total; flat += BWD_PR_MAIN_TAIL_BLOCK_THREADS) {
    const u32 source = flat / output_stride;
    const u32 row = flat - source * output_stride;
    const pr *leaves = desc.entry + static_cast<size_t>(source) * desc.entry_column_elems + 8u * row;
    const pr leaf_zero = leaves[0];
    pr folded = leaf_zero;
#pragma unroll
    for (u32 q = 1; q < 8; ++q)
      folded = pr::fma(pr::sub(leaves[q], leaf_zero), weights[q - 1], folded);
    desc.ping[static_cast<size_t>(source) * output_stride + row] = folded;
  }
}

DEVICE_FORCEINLINE void bwd_pr_main_tail_fold_d1(const bwd_pr_main_tail_desc &desc, const pr *input, const u32 input_stride, pr *output,
                                                 const u32 output_stride, const pr challenge) {
  const u32 total = u32{desc.source_count} * output_stride;
  for (u32 flat = threadIdx.x; flat < total; flat += BWD_PR_MAIN_TAIL_BLOCK_THREADS) {
    const u32 source = flat / output_stride;
    const u32 row = flat - source * output_stride;
    const pr *pair = input + static_cast<size_t>(source) * input_stride + 2u * row;
    output[static_cast<size_t>(source) * output_stride + row] = pr::fma(pr::sub(pair[1], pair[0]), challenge, pair[0]);
  }
}

struct bwd_pr_main_tail_pair {
  pr endpoint0;
  pr delta;
};

DEVICE_FORCEINLINE bwd_pr_main_tail_pair bwd_pr_main_tail_resolve(const pr *columns, const u32 stride, const u32 row, const u16 source, const bool pair) {
  const pr *values = columns + static_cast<size_t>(source) * stride + 2u * row;
  const pr endpoint0 = values[0];
  if (!pair)
    return bwd_pr_main_tail_pair{endpoint0, pr::ZERO()};
  return bwd_pr_main_tail_pair{endpoint0, pr::sub(values[1], endpoint0)};
}

DEVICE_FORCEINLINE void bwd_pr_main_tail_apply_immediate(const pr *immediates, const u16 immediate_id, const pr &value, pr &sum) {
  if (immediate_id == BWD_PROGRAM_IMMEDIATE_ONE) {
    sum = pr::add(sum, value);
  } else if (immediate_id == BWD_PROGRAM_IMMEDIATE_NEG_ONE) {
    sum = pr::sub(sum, value);
  } else {
    sum = pr::fma(value, immediates[immediate_id - BWD_PROGRAM_IMMEDIATE_RESERVED], sum);
  }
}

DEVICE_FORCEINLINE void bwd_pr_main_tail_evaluate_list(const bwd_pr_main_tail_desc &desc, const u16 *program, u32 pc, const u32 pc_end, const bool apply_c_init,
                                                       const pr *columns, const u32 stride, const u32 row, pr &acc_c0, pr &acc_c2) {
  acc_c0 = pr::ZERO();
  acc_c2 = pr::ZERO();
  if (apply_c_init && desc.c_init_coeff_id != BWD_PR_MAIN_TAIL_C_INIT_NONE)
    acc_c0 = desc.coefficients[desc.c_init_coeff_id];

#pragma unroll 1
  for (; pc < pc_end; pc += BWD_CONTINUATION_WORDS_PER_TERM) {
    const u16 header = program[pc];
    const u16 term_class = (header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
    const u16 coefficient_index = (header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
    const u16 source_a = program[pc + 1];
    const u16 source_b = program[pc + 2];

    if (term_class == BWD_CONTINUATION_CLASS_GROUP_HEADER) {
      const u16 member_count = source_a;
      const u16 flags = source_b;
      pr sum_c0 = pr::ZERO();
      pr sum_c2 = pr::ZERO();
#pragma unroll 1
      for (u16 member = 0; member < member_count; member++) {
        pc += BWD_CONTINUATION_WORDS_PER_TERM;
        const u16 member_header = program[pc];
        const u16 member_class = (member_header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
        const u16 immediate_id = (member_header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
        if (member_class == BWD_CONTINUATION_CLASS_C0_LINEAR_E4) {
          const bwd_pr_main_tail_pair a = bwd_pr_main_tail_resolve(columns, stride, row, program[pc + 1], false);
          bwd_pr_main_tail_apply_immediate(desc.immediates, immediate_id, a.endpoint0, sum_c0);
        } else if (member_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
          const bwd_pr_main_tail_pair a = bwd_pr_main_tail_resolve(columns, stride, row, program[pc + 1], true);
          const bwd_pr_main_tail_pair b = bwd_pr_main_tail_resolve(columns, stride, row, program[pc + 2], true);
          bwd_pr_main_tail_apply_immediate(desc.immediates, immediate_id, pr::mul(a.endpoint0, b.endpoint0), sum_c0);
          bwd_pr_main_tail_apply_immediate(desc.immediates, immediate_id, pr::mul(a.delta, b.delta), sum_c2);
        }
      }
      const pr core = desc.coefficients[coefficient_index];
      if ((flags & BWD_CONTINUATION_GROUP_FLAG_C0) != 0)
        acc_c0 = pr::fma(core, sum_c0, acc_c0);
      if ((flags & BWD_CONTINUATION_GROUP_FLAG_C2) != 0)
        acc_c2 = pr::fma(core, sum_c2, acc_c2);
      continue;
    }

    const pr coefficient = desc.coefficients[coefficient_index];
    if (term_class == BWD_CONTINUATION_CLASS_C0_LINEAR_E4) {
      const bwd_pr_main_tail_pair a = bwd_pr_main_tail_resolve(columns, stride, row, source_a, false);
      acc_c0 = pr::fma(coefficient, a.endpoint0, acc_c0);
    } else if (term_class == BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4) {
      const bwd_pr_main_tail_pair a = bwd_pr_main_tail_resolve(columns, stride, row, source_a, true);
      const bwd_pr_main_tail_pair b = bwd_pr_main_tail_resolve(columns, stride, row, source_b, true);
      acc_c0 = pr::fma(coefficient, pr::mul(a.endpoint0, b.endpoint0), acc_c0);
      acc_c2 = pr::fma(coefficient, pr::mul(a.delta, b.delta), acc_c2);
    }
  }
}

DEVICE_FORCEINLINE pr bwd_pr_main_tail_reduce_plane(const bwd_pr_main_tail_desc &desc, const gkr_eq_sizes &eq_sizes, const pr value, const bool active,
                                                    pr (&plane)[BWD_PR_MAIN_TAIL_BLOCK_THREADS]) {
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  plane[threadIdx.x] = value;
  __syncthreads();
  pr row_value = pr::ZERO();
  if (warp == 0) {
#pragma unroll
    for (u32 list = 0; list < BWD_PR_MAIN_TAIL_K; ++list)
      row_value = pr::add(row_value, plane[list * BWD_WINDOW_WARP_LANES + lane]);
    const pr eq = gkr_compute_eq_inline_global<pr>(desc.eq_high, desc.eq_high + GKR_EQ_GROUP_TABLE_LEN, desc.eq_low, eq_sizes, active ? lane : 0);
    row_value = pr::mul(row_value, eq);
  }
  return gkr_trace_holder_partials_warp_reduce_sum<pr>(row_value);
}

DEVICE_FORCEINLINE void bwd_pr_main_tail_evaluate_round(const bwd_pr_main_tail_desc &desc, const u8 *program_blob, const pr *columns, const u32 stride,
                                                        const gkr_eq_sizes &eq_sizes, pr (&plane)[BWD_PR_MAIN_TAIL_BLOCK_THREADS], pr &e_partial,
                                                        pr &c_partial) {
  const u32 lane = threadIdx.x & BWD_WINDOW_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_WINDOW_WARP_SHIFT;
  const u32 rows = stride >> 1;
  const bool active = lane < rows;
  const u16 *list_offsets = bwd_pr_main_tail_list_offsets(program_blob);
  pr part_c0;
  pr part_c2;
  bwd_pr_main_tail_evaluate_list(desc, bwd_pr_main_tail_program(program_blob), list_offsets[warp], list_offsets[warp + 1], warp == 0, columns, stride,
                                 active ? lane : 0, part_c0, part_c2);
  if (!active) {
    part_c0 = pr::ZERO();
    part_c2 = pr::ZERO();
  }
  const pr row_c0 = bwd_pr_main_tail_reduce_plane(desc, eq_sizes, part_c0, active, plane);
  if (threadIdx.x == 0)
    e_partial = row_c0;
  __syncthreads();
  const pr row_c2 = bwd_pr_main_tail_reduce_plane(desc, eq_sizes, part_c2, active, plane);
  if (threadIdx.x == 0)
    c_partial = row_c2;
  __syncthreads();
}

DEVICE_FORCEINLINE bool bwd_pr_main_tail_valid(const bwd_pr_main_tail_desc &desc, const u8 *program_blob) {
  const u32 tail_rounds = u32{desc.folding_steps} - u32{desc.tail_start};
  return blockDim.x == BWD_PR_MAIN_TAIL_BLOCK_THREADS && gridDim.x == 1 && desc.source_count != 0 && desc.source_count <= BWD_PR_MAIN_TAIL_SOURCE_CAP &&
         desc.program_words <= BWD_PR_MAIN_TAIL_PROGRAM_WORD_CAP && desc.program_words % BWD_CONTINUATION_WORDS_PER_TERM == 0 &&
         desc.immediate_count <= BWD_PR_MAIN_TAIL_IMMEDIATE_CAP && (desc.immediate_count == 0 || desc.immediates != nullptr) && desc.tail_start >= 3 &&
         desc.folding_steps > desc.tail_start && tail_rounds <= 6 && desc.entry_column_elems == (8u << tail_rounds) && desc.eq_sizes.high[0] == 0 &&
         desc.eq_sizes.high[1] == 0 && desc.eq_sizes.low == tail_rounds - 1 &&
         bwd_pr_main_tail_list_offsets(program_blob)[BWD_PR_MAIN_TAIL_K] == desc.program_words;
}

DEVICE_FORCEINLINE void bwd_pr_main_tail_execute(const bwd_pr_main_tail_desc &desc, const u8 *program_blob) {
  __shared__ pr plane[BWD_PR_MAIN_TAIL_BLOCK_THREADS];
  __shared__ pr d3_weights[BWD_PR_MAIN_TAIL_D3_WEIGHTS];
  __shared__ pr e_partial;
  __shared__ pr c_partial;
  __shared__ pr challenge;
  __shared__ gkr_eq_sizes eq_sizes;

  const u32 tail_rounds = u32{desc.folding_steps} - u32{desc.tail_start};
  if (threadIdx.x == 0)
    eq_sizes = desc.eq_sizes;
  bwd_pr_main_tail_build_d3_weights(desc, d3_weights);
  __syncthreads();
  bwd_pr_main_tail_fold_d3(desc, desc.entry_column_elems >> 3, d3_weights);

  const pr *input = desc.entry;
  pr *output = desc.ping;
  u32 input_stride = desc.entry_column_elems;
  for (u32 iteration = 0; iteration < tail_rounds; ++iteration) {
    const u32 output_stride = iteration == 0 ? input_stride >> 3 : input_stride >> 1;
    if (iteration != 0)
      bwd_pr_main_tail_fold_d1(desc, input, input_stride, output, output_stride, challenge);
    __syncthreads();

    bwd_pr_main_tail_evaluate_round(desc, program_blob, output, output_stride, eq_sizes, plane, e_partial, c_partial);
    const u32 absolute_round = u32{desc.tail_start} + iteration;
    if (threadIdx.x == 0) {
      const pr previous_coordinate = desc.prev_claim_coordinates[absolute_round];
      pr drawn;
      run_round_update_single_thread_pr(e_partial, c_partial, previous_coordinate, desc.seed, desc.claim, desc.eq_prefactor,
                                        desc.coefficients_out + 4u * absolute_round, &drawn);
      challenge = drawn;
      desc.challenges_out[absolute_round] = drawn;
    }
    __syncthreads();

    if (iteration + 1 < tail_rounds) {
      fold_active_eq_slot_pr<BWD_PR_MAIN_TAIL_BLOCK_THREADS>(desc.eq_low, eq_sizes.low);
      if (threadIdx.x == 0)
        --eq_sizes.low;
      __syncthreads();
    }

    input = output;
    input_stride = output_stride;
    output = output == desc.ping ? desc.pong : desc.ping;
  }
}

} // namespace airbender::gkr::proth120::backward
