#pragma once

// Chunked deferred reduction with packed carry words: the
// four coefficients of a cell keep individual lo/mid words but share one
// register for their high words, one byte each. Products follow e4::mul;
// accumulator_bounds.cuh proves that each carry byte stays independent.
// State per cell is nine 32-bit words.

#include "accumulator_bounds.cuh"

namespace airbender::gkr::backward {

// Each coefficient's high word is <= DR_WINDOW_WIDE_MAX_HIGH_WORD (8) for at
// most 40 products, so a byte can never overflow into its neighbour and the
// four bytes stay independent without cross-byte carry handling.
static_assert(DR_WINDOW_WIDE_MAX_HIGH_WORD < 256, "packed carry bytes must hold the bounded high word");

struct dr_window_packed_carry_e4 {
  u32 lo[4] = {0, 0, 0, 0};
  u32 mid[4] = {0, 0, 0, 0};
  u32 packed_hi = 0;

  // Fold one u64 chunk (< 4 * (p-1)^2) into coefficient `index`; the carry out
  // of the 64-bit add lands in byte `index` of packed_hi.
  template <u32 INDEX> DEVICE_FORCEINLINE void add_u64(const u64 value) {
    static_assert(INDEX < 4, "E4 has four coefficients");
    lo[INDEX] = add_cc(lo[INDEX], static_cast<u32>(value));
    mid[INDEX] = addc_cc(mid[INDEX], static_cast<u32>(value >> 32));
    const u32 carry = addc(0u, 0u);
    packed_hi += carry << (8u * INDEX);
  }

  DEVICE_FORCEINLINE bf reduce_coefficient(const u32 index) const {
    const u64 low = static_cast<u64>(lo[index]) | (static_cast<u64>(mid[index]) << 32);
    const u32 hi = (packed_hi >> (8u * index)) & 0xffu;
    return bf::add(bf::red_wide(low), dr_window_wide_high_word(hi));
  }

  DEVICE_FORCEINLINE e4 reduce() const { return e4(e2(reduce_coefficient(0), reduce_coefficient(1)), e2(reduce_coefficient(2), reduce_coefficient(3))); }
};

static_assert(sizeof(dr_window_packed_carry_e4) == 36, "DR packed-carry accumulator layout drift");

// total[x2] += coefficient * value.values[x2], raw; same product table and
// prescale as e4::mul.
DEVICE_FORCEINLINE void dr_window_accumulate_triplet(dr_window_packed_carry_e4 (&total)[3], const bwd_window_triplet<e4> value, const e4 coefficient) {
  const u32 a0 = coefficient[0][0].limb;
  const u32 a1 = coefficient[0][1].limb;
  const u32 a2 = coefficient[1][0].limb;
  const u32 a3 = coefficient[1][1].limb;
  const u32 a1n = bf::mul_by_non_residue(bf(a1)).limb;
  const u32 a2n = bf::mul_by_non_residue(bf(a2)).limb;
  const u32 a3n = bf::mul_by_non_residue(bf(a3)).limb;
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    const e4 &v = value.values[x2];
    const u32 b0 = v[0][0].limb;
    const u32 b1 = v[0][1].limb;
    const u32 b2 = v[1][0].limb;
    const u32 b3 = v[1][1].limb;
    dr_window_packed_carry_e4 &cell = total[x2];

    u64 acc = mul_wide(a0, b0);
    acc = mad_wide(a1n, b1, acc);
    acc = mad_wide(a2n, b3, acc);
    acc = mad_wide(a3n, b2, acc);
    cell.add_u64<0>(acc);

    acc = mul_wide(a0, b1);
    acc = mad_wide(a1, b0, acc);
    acc = mad_wide(a2, b2, acc);
    acc = mad_wide(a3n, b3, acc);
    cell.add_u64<1>(acc);

    acc = mul_wide(a0, b2);
    acc = mad_wide(a1n, b3, acc);
    acc = mad_wide(a2, b0, acc);
    acc = mad_wide(a3n, b1, acc);
    cell.add_u64<2>(acc);

    acc = mul_wide(a0, b3);
    acc = mad_wide(a1, b2, acc);
    acc = mad_wide(a2, b1, acc);
    acc = mad_wide(a3, b0, acc);
    cell.add_u64<3>(acc);
  }
}

} // namespace airbender::gkr::backward
