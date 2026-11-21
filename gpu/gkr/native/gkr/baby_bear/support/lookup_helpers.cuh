#pragma once

#include "gkr/baby_bear/support/eq_inline.cuh"
#include "gkr/baby_bear/support/kernel_helpers.cuh"
#include "gkr/support/lookup_helpers.cuh"

namespace airbender::gkr {

template <typename E>
DEVICE_FORCEINLINE void gkr_forward_setup_generic_lookup(const gkr_forward_setup_generic_lookup_batch<E> &batch, const unsigned row_count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;

  // Thread 0 also writes the forward VM's scalar fills, zero when absent: the decoder fill
  // alpha^(column_count-1) * decoder_table_id and the setup padding fill padding * sum(alpha^j).
  if (gid == 0) {
    if (batch.decoder_fill_value_out != nullptr) {
      E fill = E::ZERO();
      if (batch.decoder_table_id != 0 && batch.column_count > 0)
        fill = E::mul(::ab_gkr_lookup_alpha_powers[batch.column_count - 1], bf::from_u32_unchecked(batch.decoder_table_id));
      store<E, st_modifier::cs>(batch.decoder_fill_value_out, fill, 0);
    }
    if (batch.padding_fill_value_out != nullptr) {
      E fill = E::ZERO();
      if (batch.padding_value.limb != 0) {
        for (unsigned j = 0; j < batch.column_count; ++j)
          fill = E::add(fill, ::ab_gkr_lookup_alpha_powers[j]);
        fill = E::mul(fill, batch.padding_value);
      }
      store<E, st_modifier::cs>(batch.padding_fill_value_out, fill, 0);
    }
  }

  if (gid >= row_count)
    return;

  E value = E::ZERO();

#pragma unroll
  for (unsigned column_idx = 0; column_idx < GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS; ++column_idx) {
    if (column_idx >= batch.column_count)
      break;

    const auto descriptor = batch.descriptors[column_idx];
    const bf input = load<bf, ld_modifier::cs>(descriptor.input, gid);
    const E alpha_power = ::ab_gkr_lookup_alpha_powers[column_idx];
    value = E::fma(alpha_power, input, value);
  }

  store<E, st_modifier::cs>(batch.output, value, gid);
}

// Loads a slot's 2 batch challenges from the __constant__ table.
DEVICE_FORCEINLINE void gkr_load_slot_batch_challenges(const gkr_dim_reducing_slot &slot, e4 (&bc)[GKR_DIM_REDUCING_OUTPUTS_PER_SLOT]) {
#pragma unroll
  for (unsigned t = 0; t < GKR_DIM_REDUCING_OUTPUTS_PER_SLOT; ++t)
    bc[t] = ::ab_gkr_dim_reducing_batch_challenge_table[slot.batch_exp[t]];
}

} // namespace airbender::gkr
