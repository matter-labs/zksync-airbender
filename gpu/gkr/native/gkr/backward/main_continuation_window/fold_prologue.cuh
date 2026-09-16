#pragma once

#include "../window/window_accumulator.cuh"
#include "main_continuation_window_abi.cuh"

namespace airbender::gkr::backward {

using ::airbender::primitives::memory::ld_modifier;
using ::airbender::primitives::memory::load;
using ::airbender::primitives::memory::st_modifier;
using ::airbender::primitives::memory::store;

struct alignas(32) bwd_main_cont_bf8 {
  bf value[8];
};

struct alignas(32) bwd_main_cont_e4_pair {
  e4 value[2];
};

static_assert(sizeof(bwd_main_cont_bf8) == 32 && alignof(bwd_main_cont_bf8) == 32, "BF leaf packet must be one aligned 256-bit load");
static_assert(sizeof(bwd_main_cont_e4_pair) == 32 && alignof(bwd_main_cont_e4_pair) == 32, "E4 pair must be one aligned 256-bit transaction");

using ::airbender::primitives::ptx::mad_wide;
using ::airbender::primitives::ptx::mul_wide;

// Every term chunk has at most four reduced-limb products, hence fits u64.
// Seven E4 chunks plus the Montgomery-scaled seed are below 2^67; the BF
// path is below 2^66. The u96 reducer accounts for hi * 2^64.
static_assert(bf::ORDER < (1u << 31), "fold chunk and accumulator bounds");
DEVICE_FORCEINLINE void bwd_main_cont_fold_add_chunk(bwd_window_u96_accumulator &acc, const u64 chunk) {
  asm volatile("{\n\t"
               ".reg .u32 al, ah, bl, bh;\n\t"
               "mov.b64 {al, ah}, %0;\n\t"
               "mov.b64 {bl, bh}, %2;\n\t"
               "add.cc.u32 al, al, bl;\n\t"
               "addc.cc.u32 ah, ah, bh;\n\t"
               "addc.u32 %1, %1, 0;\n\t"
               "mov.b64 %0, {al, ah};\n\t"
               "}"
               : "+l"(acc.low), "+r"(acc.hi)
               : "l"(chunk));
}

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_bf_wide(const bwd_main_cont_bf8 &leaves) {
  bf differences[7];
#pragma unroll
  for (u32 q = 1; q < 8; ++q)
    differences[q - 1] = bf::sub(leaves.value[q], leaves.value[0]);
  bf output[4];
#pragma unroll
  for (u32 i = 0; i < 4; ++i) {
    bwd_window_u96_accumulator acc;
    acc.low = i == 0 ? u64(leaves.value[0].limb) << 32 : 0;
    u64 chunk = 0;
#pragma unroll
    for (u32 q = 0; q < 4; ++q) {
      const e4 weight = ::ab_gkr_bwd_fold_weights[BWD_FOLD_WEIGHT_BASE_D3 + q];
      chunk = mad_wide(weight[i / 2][i % 2].limb, differences[q].limb, chunk);
    }
    bwd_main_cont_fold_add_chunk(acc, chunk);
    chunk = 0;
#pragma unroll
    for (u32 q = 4; q < 7; ++q) {
      const e4 weight = ::ab_gkr_bwd_fold_weights[BWD_FOLD_WEIGHT_BASE_D3 + q];
      chunk = mad_wide(weight[i / 2][i % 2].limb, differences[q].limb, chunk);
    }
    bwd_main_cont_fold_add_chunk(acc, chunk);
    output[i] = acc.reduce();
  }
  return e4(output);
}

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_e4_wide(const bwd_main_cont_e4_pair (&packets)[4]) {
  const e4 seed = packets[0].value[0];
  bwd_window_u96_accumulator acc[4];
#pragma unroll
  for (u32 i = 0; i < 4; ++i)
    acc[i].low = u64(seed[i / 2][i % 2].limb) << 32;
#pragma unroll
  for (u32 q = 1; q < 8; ++q) {
    const e4 w = ::ab_gkr_bwd_fold_weights[BWD_FOLD_WEIGHT_BASE_D3 + q - 1];
    const e4 d = e4::sub(packets[q >> 1].value[q & 1], seed);
    const u32 a0 = w[0][0].limb, a1 = w[0][1].limb, a2 = w[1][0].limb, a3 = w[1][1].limb;
    const u32 b0 = d[0][0].limb, b1 = d[0][1].limb, b2 = d[1][0].limb, b3 = d[1][1].limb;
    const u32 n1 = bf::mul_by_non_residue(bf(a1)).limb;
    const u32 n2 = bf::mul_by_non_residue(bf(a2)).limb;
    const u32 n3 = bf::mul_by_non_residue(bf(a3)).limb;
    u64 chunk = mul_wide(a0, b0);
    chunk = mad_wide(n1, b1, chunk);
    chunk = mad_wide(n2, b3, chunk);
    chunk = mad_wide(n3, b2, chunk);
    bwd_main_cont_fold_add_chunk(acc[0], chunk);
    chunk = mul_wide(a0, b1);
    chunk = mad_wide(a1, b0, chunk);
    chunk = mad_wide(a2, b2, chunk);
    chunk = mad_wide(n3, b3, chunk);
    bwd_main_cont_fold_add_chunk(acc[1], chunk);
    chunk = mul_wide(a0, b2);
    chunk = mad_wide(n1, b3, chunk);
    chunk = mad_wide(a2, b0, chunk);
    chunk = mad_wide(n3, b1, chunk);
    bwd_main_cont_fold_add_chunk(acc[2], chunk);
    chunk = mul_wide(a0, b3);
    chunk = mad_wide(a1, b2, chunk);
    chunk = mad_wide(a2, b1, chunk);
    chunk = mad_wide(a3, b0, chunk);
    bwd_main_cont_fold_add_chunk(acc[3], chunk);
  }
  bf output[4];
#pragma unroll
  for (u32 i = 0; i < 4; ++i)
    output[i] = acc[i].reduce();
  return e4(output);
}

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_bf_packet(const bwd_main_cont_bf8 &leaves) {
  constexpr u32 weight_base = BWD_FOLD_WEIGHT_BASE_D3;
  const bf leaf0 = leaves.value[0];
  e4 accumulator = e4::from_scalar(leaf0);
#pragma unroll
  for (u32 q = 1; q < 8; q++) {
    const e4 weight = ::ab_gkr_bwd_fold_weights[weight_base + q - 1];
    accumulator = e4::fma(weight, bf::sub(leaves.value[q], leaf0), accumulator);
  }
  return accumulator;
}

DEVICE_FORCEINLINE e4 bwd_main_cont_fold_e4_packets(const bwd_main_cont_e4_pair (&packets)[4]) {
  constexpr u32 weight_base = BWD_FOLD_WEIGHT_BASE_D3;
  const e4 leaf0 = packets[0].value[0];
  e4 accumulator = leaf0;
#pragma unroll
  for (u32 q = 1; q < 8; q++) {
    const e4 leaf = packets[q >> 1].value[q & 1];
    const e4 weight = ::ab_gkr_bwd_fold_weights[weight_base + q - 1];
    accumulator = e4::fma(weight, e4::sub(leaf, leaf0), accumulator);
  }
  return accumulator;
}

template <bool WideFold = false>
DEVICE_FORCEINLINE e4 bwd_main_cont_fold_output(const bwd_main_cont_window_desc &desc, const bwd_main_cont_window_source_record &record,
                                                const bwd_source_window &input_slot, const u32 output_index) {
  if (desc.publication_fold == 0) {
    // The zero-continuation chain needs the exact depth-zero source arena in
    // canonical E4 form. Base and virtual sources are embedded without a host
    // round trip; extension sources retain their original bytes.
    if (input_slot.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
      const gkr_base_source_kind kind = bwd_coeff_procedural_source_kind(input_slot.procedural_kind);
      return e4::from_scalar(gkr_virtual_base_value(kind, output_index));
    }
    if (input_slot.origin == BWD_COEFF_ORIGIN_READ_EXT) {
      const e4 *input = bwd_main_cont_window_column<e4>(desc, record.src);
      return load<e4, ld_modifier::cs>(input, output_index);
    }
    const bf *input = bwd_main_cont_window_column<bf>(desc, record.src);
    return e4::from_scalar(load<bf, ld_modifier::cs>(input, output_index));
  }
  const u32 leaf_index = output_index << 3;
  if (input_slot.origin == BWD_COEFF_ORIGIN_PROCEDURAL) {
    const gkr_base_source_kind kind = bwd_coeff_procedural_source_kind(input_slot.procedural_kind);
    bwd_main_cont_bf8 leaves;
#pragma unroll
    for (u32 q = 0; q < 8; q++)
      leaves.value[q] = gkr_virtual_base_value(kind, leaf_index + q);
    if constexpr (WideFold)
      return bwd_main_cont_fold_bf_wide(leaves);
    else
      return bwd_main_cont_fold_bf_packet(leaves);
  }
  if (input_slot.origin == BWD_COEFF_ORIGIN_READ_EXT) {
    const e4 *input = bwd_main_cont_window_column<e4>(desc, record.src) + leaf_index;
    bwd_main_cont_e4_pair packets[4];
#pragma unroll
    for (u32 pair = 0; pair < 4; pair++)
      packets[pair] = load<bwd_main_cont_e4_pair, ld_modifier::cs>(reinterpret_cast<const bwd_main_cont_e4_pair *>(input) + pair);
    if constexpr (WideFold)
      return bwd_main_cont_fold_e4_wide(packets);
    else
      return bwd_main_cont_fold_e4_packets(packets);
  }
  const bf *input = bwd_main_cont_window_column<bf>(desc, record.src) + leaf_index;
  const bwd_main_cont_bf8 leaves = load<bwd_main_cont_bf8, ld_modifier::cs>(reinterpret_cast<const bwd_main_cont_bf8 *>(input));
  if constexpr (WideFold)
    return bwd_main_cont_fold_bf_wide(leaves);
  else
    return bwd_main_cont_fold_bf_packet(leaves);
}

// Four adjacent lanes cooperatively publish one suffix row. Each lane owns one
// aligned pair of Boolean corners, so the canonical row-major arena remains
// unchanged while the fold's live state is two E4 values instead of eight.
// Input indices are `(row << 6) + (corner << 3) + q`: corner carries the three
// window coordinates and q carries the preceding delta-3 fold coordinates.
template <bool WideFold = false>
DEVICE_FORCEINLINE void bwd_main_cont_fold_source_pair(const bwd_main_cont_window_desc &desc, const u16 source_id, const u32 row, const bool active,
                                                       const u32 corner_pair) {
  const bwd_main_cont_window_source_record record = desc.source[source_id];
  const bwd_source_window &input_slot = desc.slot[bwd_main_cont_window_lane_slot(record.src)];
  e4 outputs[2];
#pragma unroll
  for (u32 offset = 0; offset < 2; offset++)
    outputs[offset] = bwd_main_cont_fold_output<WideFold>(desc, record, input_slot, (row << 3) + 2 * corner_pair + offset);

  if (!active)
    return;
  e4 *publish = bwd_main_cont_window_column_mut(desc, record.publish) + (row << 3) + 2 * corner_pair;
  const bwd_main_cont_e4_pair values{{outputs[0], outputs[1]}};
  store<bwd_main_cont_e4_pair, st_modifier::wb>(reinterpret_cast<bwd_main_cont_e4_pair *>(publish), values);
}

template <bool WideFold = false>
DEVICE_FORCEINLINE void bwd_main_cont_fold_prologue_pair(const bwd_main_cont_window_desc &desc, const u32 warp_id, const u32 row, const bool active,
                                                         const u32 corner_pair) {
  const u32 begin = desc.fold_list_offsets[warp_id];
  const u32 end = desc.fold_list_offsets[warp_id + 1];
  for (u32 position = begin; position < end; position++)
    bwd_main_cont_fold_source_pair<WideFold>(desc, desc.fold_sources[position], row, active, corner_pair);
}

} // namespace airbender::gkr::backward
