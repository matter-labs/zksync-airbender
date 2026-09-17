#pragma once

#include "window_abi.cuh"

#include <type_traits>

namespace airbender::gkr::backward {

// The u96 accumulator's high word represents hi * 2^64 in a sum of raw
// Montgomery products. After Montgomery reduction it contributes hi * 2^32,
// i.e. the Montgomery representation of hi. Express that scale directly in
// raw Montgomery form; this is runtime carry arithmetic, not integer decoding.
DEVICE_FORCEINLINE bf bwd_window_high_word_contribution(const u32 hi) { return bf::mul(bf::from_reduced_raw_repr(hi), bf::from_reduced_raw_repr(bf::MONT_R2)); }

// Deferred-reduction accumulator for raw 32x32 Montgomery products. Keep the
// low two words in one u64 operand so ptxas can use aligned register pairs
// without copying the words around each multiply-add. The single asm block
// preserves the carry chain; reduction includes the high-word term.
// Padding is thread-local: this type does not cross a memory or launch ABI.
struct bwd_window_u96_accumulator {
  u64 low = 0;
  u32 hi = 0;
  DEVICE_FORCEINLINE void add_product(const u32 a, const u32 b) {
    asm volatile("{\n\t"
                 ".reg .u32 lo, mid;\n\t"
                 "mov.b64 {lo, mid}, %0;\n\t"
                 "mad.lo.cc.u32 lo, %2, %3, lo;\n\t"
                 "madc.hi.cc.u32 mid, %2, %3, mid;\n\t"
                 "addc.u32 %1, %1, 0;\n\t"
                 "mov.b64 %0, {lo, mid};\n\t"
                 "}"
                 : "+l"(low), "+r"(hi)
                 : "r"(a), "r"(b));
  }
  DEVICE_FORCEINLINE bf reduce() const { return bf::add(bf::red_wide(low), bwd_window_high_word_contribution(hi)); }
};
static_assert(sizeof(bwd_window_u96_accumulator) == 16, "u96 accumulator layout drift");
static_assert(std::is_trivially_copyable_v<bwd_window_u96_accumulator>);
static_assert(bwd_window_u96_accumulator{}.low == 0 && bwd_window_u96_accumulator{}.hi == 0);
} // namespace airbender::gkr::backward
