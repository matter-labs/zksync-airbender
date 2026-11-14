#include "primitives/field.cuh"
#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::forward {
using pr = ::airbender::primitives::field::proth120;
struct challenge_power_slot {
  u32 source;
  u32 power;
};
struct forward_challenge_desc {
  challenge_power_slot slots[12];
  u32 arg_count;
  u32 lookup_slot;
  u32 decoder_slot;
  u32 table_width;
  u32 decoder_table_id;
};
static_assert(sizeof(challenge_power_slot) == 8);
static_assert(sizeof(forward_challenge_desc) == 116);
static_assert(alignof(forward_challenge_desc) == 4);
static_assert(4 * sizeof(void *) + sizeof(forward_challenge_desc) <= 32764);
DEVICE_FORCEINLINE pr power(pr base, u32 exponent) {
  pr value = pr::ONE();
  while (exponent != 0) {
    if (exponent & 1)
      value = pr::mul(value, base);
    exponent >>= 1;
    base = pr::mul(base, base);
  }
  return value;
}
EXTERN __global__ void ab_pr_gkr_forward_challenge_banks_kernel(const pr *challenges, pr *arg_derived, pr *const_derived, pr *lookup_alpha_powers,
                                                                const forward_challenge_desc plan) {
  if (threadIdx.x != 0)
    return;
  for (u32 i = 0; i < 12; ++i)
    arg_derived[i] = i < plan.arg_count ? power(challenges[plan.slots[i].source], plan.slots[i].power) : pr::ZERO();
  for (u32 i = 0; i < 8; ++i)
    const_derived[i] = pr::ZERO();
  pr alpha_power = pr::ONE();
  for (u32 i = 0; i < 11; ++i) {
    lookup_alpha_powers[i] = alpha_power;
    alpha_power = pr::mul(alpha_power, challenges[7]);
  }
  if (plan.lookup_slot != 0xffffffffu)
    const_derived[plan.lookup_slot] = challenges[8];
  if (plan.decoder_slot != 0xffffffffu) {
    const u32 natural[4] = {plan.decoder_table_id, 0, 0, 0};
    const_derived[plan.decoder_slot] =
        plan.table_width == 0 ? pr::ZERO() : pr::mul(lookup_alpha_powers[plan.table_width - 1], pr::from_u128_with_reduction(natural));
  }
}
} // namespace airbender::gkr::proth120::forward
