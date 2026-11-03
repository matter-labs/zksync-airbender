#pragma once
#include "abi.cuh"

namespace airbender::gkr::backward {
// Bound: every operand limb is canonical (< p), including the pre-scaled
// 11 * a_i limbs (bf::mul_by_non_residue returns from_lt_2_order_u32). One
// cell accumulates at most 5 slots x 2 outputs = 10 weightings x 4 raw
// products per coefficient = 40 products, each <= (p - 1)^2. With
// p - 1 = 15 * 2^27: 40 * (p - 1)^2 = 40 * 225 * 2^54 = 9000 * 2^54, and
// 9000 < 9 * 1024, so the sum is < 9 * 2^64 and the high word hi <= 8.
constexpr u32 DR_WINDOW_WIDE_MAX_HIGH_WORD = 8;
static_assert(bf::ORDER == 0x78000001u, "DR wide accumulator bound assumes the BabyBear modulus");
static_assert(bf::ORDER - 1u == 15u * (1u << 27), "DR wide accumulator bound assumes p - 1 = 15 * 2^27");
static_assert(4 * GKR_DIM_REDUCING_SLOTS * GKR_DIM_REDUCING_OUTPUTS_PER_SLOT == 40, "DR wide accumulator bound assumes 40 products per coefficient");
static_assert(40u * 225u < (DR_WINDOW_WIDE_MAX_HIGH_WORD + 1u) * 1024u, "40 * (p - 1)^2 must stay below 9 * 2^64");
// The high word represents hi * 2^64 in a sum of raw products; after Montgomery
// reduction it contributes hi * 2^32 mod p = hi * (2^28 - 2), which for
// hi <= 8 is <= 2^31 - 16 < 2p and needs a single conditional subtraction.
static_assert(bf::MONT_R_U64 == (1ull << 28) - 2ull, "2^32 mod p must equal 2^28 - 2");
static_assert(static_cast<u64>(DR_WINDOW_WIDE_MAX_HIGH_WORD) * bf::MONT_R_U64 < 2ull * bf::ORDER, "hi * MONT_R must stay below 2p");

DEVICE_FORCEINLINE bf dr_window_wide_high_word(const u32 hi) { return bf::from_lt_2_order_u32((hi << 28) - (hi << 1)); }

} // namespace airbender::gkr::backward
