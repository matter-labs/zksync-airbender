#pragma once

#include <assert.h>

#include "continuation_eval.cuh"
#include "mega_finalize.cuh"

namespace airbender::gkr::backward {

constexpr u32 BWD_MAIN_TAIL_BLOCK_THREADS = 256;
constexpr u32 BWD_MAIN_TAIL_K = 8;
constexpr u32 BWD_MAIN_TAIL_LIST_OFFSETS = BWD_MAIN_TAIL_K + 1;
constexpr u32 BWD_MAIN_TAIL_LIST_OFFSETS_OFFSET = 0;
constexpr u32 BWD_MAIN_TAIL_PROGRAM_OFFSET = 18;
constexpr u32 BWD_MAIN_TAIL_PROGRAM_WORD_CAP = 6472;
constexpr u32 BWD_MAIN_TAIL_PROGRAM_BYTES = 12944;
constexpr u32 BWD_MAIN_TAIL_IMMEDIATE_OFFSET = 12964;
constexpr u32 BWD_MAIN_TAIL_IMMEDIATE_CAP = 512;
constexpr u32 BWD_MAIN_TAIL_BLOB_BYTES = 15024;
constexpr u16 BWD_MAIN_TAIL_C_INIT_NONE = 0xffff;
constexpr u32 BWD_MAIN_TAIL_SOURCE_CAP = 1072;
constexpr u32 BWD_MAIN_TAIL_PARAMETER_CEILING = 32764;

static_assert(BWD_MAIN_TAIL_PROGRAM_OFFSET == BWD_MAIN_TAIL_LIST_OFFSETS * sizeof(u16), "main-tail program offset drift");
static_assert(BWD_MAIN_TAIL_PROGRAM_BYTES == BWD_MAIN_TAIL_PROGRAM_WORD_CAP * sizeof(u16), "main-tail program capacity drift");
static_assert(BWD_MAIN_TAIL_IMMEDIATE_OFFSET == 12964, "main-tail immediate offset drift");
static_assert(BWD_MAIN_TAIL_IMMEDIATE_OFFSET % alignof(u32) == 0, "main-tail immediate table is misaligned");
static_assert(BWD_MAIN_TAIL_BLOB_BYTES == 15024, "main-tail blob size drift");
static_assert(BWD_MAIN_TAIL_BLOB_BYTES % 16 == 0, "main-tail blob alignment drift");

struct __align__(16) bwd_main_tail_desc {
  const u8 *program_blob;
  const e4 *entry;
  e4 *ping;
  e4 *pong;
  e4 *eq_low;
  const e4 *prev_claim_coordinates;
  u32 *seed;
  e4 *claim;
  e4 *eq_prefactor;
  e4 *coefficients_out;
  e4 *challenges_out;
  gkr_eq_sizes eq_sizes;
  u32 entry_column_elems;
  u16 source_count;
  u16 program_words;
  u16 immediate_count;
  u16 c_init_coeff_id;
  u8 tail_start;
  u8 folding_steps;
  u8 k;
  u8 reserved;
  u32 blob_bytes;
  u8 tail_padding[8];
};

struct __align__(16) bwd_main_tail_program_blob {
  u8 bytes[BWD_MAIN_TAIL_BLOB_BYTES];
};

static_assert(sizeof(bwd_main_tail_desc) == 128, "main-tail descriptor size drift");
static_assert(alignof(bwd_main_tail_desc) == 16, "main-tail descriptor alignment drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, program_blob) == 0, "program_blob ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, entry) == 8, "entry ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, ping) == 16, "ping ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, pong) == 24, "pong ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, eq_low) == 32, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, prev_claim_coordinates) == 40, "prev_claim_coordinates ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, seed) == 48, "seed ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, claim) == 56, "claim ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, eq_prefactor) == 64, "eq_prefactor ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, coefficients_out) == 72, "coefficients_out ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, challenges_out) == 80, "challenges_out ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, eq_sizes) == 88, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, entry_column_elems) == 100, "entry_column_elems ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, source_count) == 104, "source_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, program_words) == 106, "program_words ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, immediate_count) == 108, "immediate_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, c_init_coeff_id) == 110, "c_init_coeff_id ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, tail_start) == 112, "tail_start ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, folding_steps) == 113, "folding_steps ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, k) == 114, "k ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, reserved) == 115, "reserved ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, blob_bytes) == 116, "blob_bytes ABI offset drift");
static_assert(__builtin_offsetof(bwd_main_tail_desc, tail_padding) == 120, "tail_padding ABI offset drift");
static_assert(sizeof(bwd_main_tail_program_blob) == BWD_MAIN_TAIL_BLOB_BYTES, "main-tail program blob size drift");
static_assert(alignof(bwd_main_tail_program_blob) == 16, "main-tail program blob alignment drift");
static_assert(sizeof(bwd_main_tail_desc) + sizeof(bwd_main_tail_program_blob) == 15152, "main-tail argument size drift");
static_assert(BWD_MAIN_TAIL_PARAMETER_CEILING - sizeof(bwd_main_tail_desc) - sizeof(bwd_main_tail_program_blob) == 17612,
              "main-tail parameter headroom drift");

DEVICE_FORCEINLINE const u16 *bwd_main_tail_list_offsets(const bwd_main_tail_desc &desc) {
  return reinterpret_cast<const u16 *>(desc.program_blob + BWD_MAIN_TAIL_LIST_OFFSETS_OFFSET);
}

DEVICE_FORCEINLINE const u16 *bwd_main_tail_program(const bwd_main_tail_desc &desc) {
  return reinterpret_cast<const u16 *>(desc.program_blob + BWD_MAIN_TAIL_PROGRAM_OFFSET);
}

DEVICE_FORCEINLINE const u32 *bwd_main_tail_immediates(const bwd_main_tail_desc &desc) {
  return reinterpret_cast<const u32 *>(desc.program_blob + BWD_MAIN_TAIL_IMMEDIATE_OFFSET);
}

DEVICE_FORCEINLINE e4 bwd_main_tail_eq_weight(const bool bit, const e4 coordinate) { return bit ? coordinate : e4::sub(e4::ONE(), coordinate); }

DEVICE_FORCEINLINE void bwd_main_tail_fold_d3(const bwd_main_tail_desc &desc, const e4 *input, const u32 input_stride, e4 *output, const u32 output_stride,
                                              const e4 (&coordinates)[3]) {
  const u32 total = u32{desc.source_count} * output_stride;
  for (u32 flat = threadIdx.x; flat < total; flat += BWD_MAIN_TAIL_BLOCK_THREADS) {
    const u32 source = flat / output_stride;
    const u32 row = flat - source * output_stride;
    const e4 *leaves = input + static_cast<size_t>(source) * input_stride + 8u * row;
    const e4 leaf_zero = leaves[0];
    e4 folded = leaf_zero;
#ifndef NDEBUG
    u32 previous_q = 0;
#endif
#pragma unroll
    for (u32 q = 1; q < 8; ++q) {
#ifndef NDEBUG
      assert(q == previous_q + 1u);
      previous_q = q;
#endif
      e4 weight = e4::ONE();
#pragma unroll
      for (u32 bit = 0; bit < 3; ++bit)
        weight = e4::mul(weight, bwd_main_tail_eq_weight(((q >> bit) & 1u) != 0, coordinates[bit]));
      folded = e4::fma(e4::sub(leaves[q], leaf_zero), weight, folded);
    }
    output[static_cast<size_t>(source) * output_stride + row] = folded;
  }
}

DEVICE_FORCEINLINE void bwd_main_tail_fold_d1(const bwd_main_tail_desc &desc, const e4 *input, const u32 input_stride, e4 *output, const u32 output_stride,
                                              const e4 challenge) {
  const u32 total = u32{desc.source_count} * output_stride;
  for (u32 flat = threadIdx.x; flat < total; flat += BWD_MAIN_TAIL_BLOCK_THREADS) {
    const u32 source = flat / output_stride;
    const u32 row = flat - source * output_stride;
    const e4 *pair = input + static_cast<size_t>(source) * input_stride + 2u * row;
    output[static_cast<size_t>(source) * output_stride + row] = e4::fma(e4::sub(pair[1], pair[0]), challenge, pair[0]);
  }
}

struct bwd_main_tail_source_pair_resolver {
  const e4 *columns;
  u32 stride;
  u32 row;

  template <bwd_continuation_projection P> DEVICE_FORCEINLINE bwd_continuation_pair resolve(const u16 source) const {
    const e4 *pair = columns + static_cast<size_t>(source) * stride + 2u * row;
    const e4 endpoint0 = pair[0];
    if constexpr (P == BWD_CONTINUATION_PROJ_ENDPOINT0)
      return bwd_continuation_pair{endpoint0, e4::ZERO()};
    return bwd_continuation_pair{endpoint0, e4::sub(pair[1], endpoint0)};
  }
};

DEVICE_FORCEINLINE e4 bwd_main_tail_warp_sum(e4 value) {
#pragma unroll
  for (u32 mask = BWD_SEG_WARP_LANES >> 1; mask != 0; mask >>= 1) {
    e4 shuffled;
    const uint4 *source = reinterpret_cast<const uint4 *>(&value);
    uint4 *destination = reinterpret_cast<uint4 *>(&shuffled);
    destination[0] = shfl_xor(0xffffffffu, source[0], mask, BWD_SEG_WARP_LANES);
    value = e4::add(value, shuffled);
  }
  return value;
}

DEVICE_FORCEINLINE void bwd_main_tail_evaluate_round(const bwd_main_tail_desc &desc, const e4 *columns, const u32 stride, const gkr_eq_sizes eq_sizes,
                                                     e4 (&plane)[BWD_MAIN_TAIL_BLOCK_THREADS], e4 &e_partial, e4 &c_partial) {
  const u32 lane = threadIdx.x & BWD_SEG_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_SEG_WARP_SHIFT;
  const u32 rows = stride >> 1;
  const bool active = lane < rows;
  const u32 safe_row = active ? lane : 0;
  const u16 *list_offsets = bwd_main_tail_list_offsets(desc);
  const bwd_main_tail_source_pair_resolver resolver{columns, stride, safe_row};
  e4 part_c0;
  e4 part_c2;
  bwd_continuation_evaluate_list(bwd_main_tail_program(desc), bwd_main_tail_immediates(desc), list_offsets[warp], list_offsets[warp + 1], warp == 0,
                                 desc.c_init_coeff_id != BWD_MAIN_TAIL_C_INIT_NONE, desc.c_init_coeff_id, resolver, part_c0, part_c2);
  if (!active) {
    part_c0 = e4::ZERO();
    part_c2 = e4::ZERO();
  }

  plane[threadIdx.x] = part_c0;
  __syncthreads();
  e4 row_c0 = e4::ZERO();
  if (warp == 0) {
#pragma unroll
    for (u32 list = 0; list < BWD_MAIN_TAIL_K; ++list)
      row_c0 = e4::add(row_c0, plane[list * BWD_SEG_WARP_LANES + lane]);
    if (active)
      row_c0 = e4::mul(row_c0, gkr_compute_eq_inline<e4>(desc.eq_low, eq_sizes, lane));
  }
  row_c0 = bwd_main_tail_warp_sum(row_c0);
  if (threadIdx.x == 0)
    e_partial = row_c0;
  __syncthreads();

  plane[threadIdx.x] = part_c2;
  __syncthreads();
  e4 row_c2 = e4::ZERO();
  if (warp == 0) {
#pragma unroll
    for (u32 list = 0; list < BWD_MAIN_TAIL_K; ++list)
      row_c2 = e4::add(row_c2, plane[list * BWD_SEG_WARP_LANES + lane]);
    if (active)
      row_c2 = e4::mul(row_c2, gkr_compute_eq_inline<e4>(desc.eq_low, eq_sizes, lane));
  }
  row_c2 = bwd_main_tail_warp_sum(row_c2);
  if (threadIdx.x == 0)
    c_partial = row_c2;
  __syncthreads();
}

DEVICE_FORCEINLINE void bwd_main_tail_execute(const bwd_main_tail_desc &desc) {
  __shared__ e4 plane[BWD_MAIN_TAIL_BLOCK_THREADS];
  __shared__ e4 d3_coordinates[3];
  __shared__ e4 e_partial;
  __shared__ e4 c_partial;
  __shared__ e4 challenge;
  __shared__ gkr_eq_sizes eq_sizes;

  const u32 tail_rounds = u32{desc.folding_steps} - u32{desc.tail_start};
  if (threadIdx.x < 3)
    // The published entry still precedes the last continuation window's
    // three folds. Bind it with those generated sumcheck challenges, not with
    // the incoming claim point used by the round-update normalization below.
    d3_coordinates[threadIdx.x] = desc.challenges_out[u32{desc.tail_start} - 3u + threadIdx.x];
  if (threadIdx.x == 0)
    eq_sizes = desc.eq_sizes;
  __syncthreads();

  const e4 *input = desc.entry;
  e4 *output = desc.ping;
  u32 input_stride = desc.entry_column_elems;
  for (u32 iteration = 0; iteration < tail_rounds; ++iteration) {
    const u32 output_stride = iteration == 0 ? input_stride >> 3 : input_stride >> 1;
    if (iteration == 0)
      bwd_main_tail_fold_d3(desc, input, input_stride, output, output_stride, d3_coordinates);
    else
      bwd_main_tail_fold_d1(desc, input, input_stride, output, output_stride, challenge);
    __syncthreads();

    bwd_main_tail_evaluate_round(desc, output, output_stride, eq_sizes, plane, e_partial, c_partial);
    const u32 absolute_round = u32{desc.tail_start} + iteration;
    if (threadIdx.x == 0) {
      const e4 previous_coordinate = desc.prev_claim_coordinates[absolute_round];
      run_round_update_single_thread(e_partial, c_partial, previous_coordinate, desc.seed, desc.claim, desc.eq_prefactor,
                                     desc.coefficients_out + 4u * absolute_round, &challenge);
      desc.challenges_out[absolute_round] = challenge;
    }
    __syncthreads();

    if (iteration + 1 < tail_rounds) {
      fold_active_eq_slot<BWD_MAIN_TAIL_BLOCK_THREADS>(desc.eq_low, eq_sizes.low);
      if (threadIdx.x == 0)
        --eq_sizes.low;
      __syncthreads();
    }

    input = output;
    input_stride = output_stride;
    output = output == desc.ping ? desc.pong : desc.ping;
  }
#ifndef NDEBUG
  if (threadIdx.x == 0)
    assert(input_stride == 2);
#endif
}

} // namespace airbender::gkr::backward
