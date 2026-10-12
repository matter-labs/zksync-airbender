#pragma once
#include "primitives/field.cuh"
#include "primitives/proth120.cuh"
namespace airbender::gkr::proth120::setup {
using pr = ::airbender::primitives::field::proth120;
struct forward_setup_lookup_batch_pr {
  u32 column_count;
  u32 decoder_table_id;
  pr *output;
  pr *decoder_fill_value_out;
  const pr *alpha_powers;
  const pr *inputs[11];
};
static_assert(sizeof(forward_setup_lookup_batch_pr) == 120);
static_assert(alignof(forward_setup_lookup_batch_pr) == 8);
static_assert(__builtin_offsetof(forward_setup_lookup_batch_pr, inputs) == 32);
static_assert(sizeof(forward_setup_lookup_batch_pr) + sizeof(u32) <= 32764);
DEVICE_FORCEINLINE void forward_setup_lookup(const forward_setup_lookup_batch_pr &batch, const u32 rows) {
  const u32 row = blockIdx.x * blockDim.x + threadIdx.x;
  if (row == 0 && batch.decoder_fill_value_out != nullptr) {
    const u32 natural[4] = {batch.decoder_table_id, 0, 0, 0};
    *batch.decoder_fill_value_out =
        batch.column_count == 0 ? pr::ZERO() : pr::mul(batch.alpha_powers[batch.column_count - 1], pr::from_u128_with_reduction(natural));
  }
  if (row >= rows)
    return;
  pr value = pr::ZERO();
  for (u32 column = 0; column < batch.column_count; ++column)
    value = pr::fma(batch.alpha_powers[column], batch.inputs[column][row], value);
  batch.output[row] = value;
}
} // namespace airbender::gkr::proth120::setup
