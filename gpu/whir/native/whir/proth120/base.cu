#include "common.cuh"
#include "primitives/proth120.cuh"
#include <cstddef>
#include <type_traits>

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::whir {

struct pr_base_columns_metadata {
  const pr *values[2];
  u32 columns[2];
  u64 strides[2];
  const pr *powers;
  pr *result;
  u32 log_rows;
  u32 pack_log2;
};

static_assert(sizeof(pr) == 16 && alignof(pr) == 16);
static_assert(sizeof(pr_base_columns_metadata) == 64 && alignof(pr_base_columns_metadata) == 8);
static_assert(offsetof(pr_base_columns_metadata, values) == 0);
static_assert(offsetof(pr_base_columns_metadata, columns) == 16);
static_assert(offsetof(pr_base_columns_metadata, strides) == 24);
static_assert(offsetof(pr_base_columns_metadata, powers) == 40);
static_assert(offsetof(pr_base_columns_metadata, result) == 48);
static_assert(offsetof(pr_base_columns_metadata, log_rows) == 56);
static_assert(offsetof(pr_base_columns_metadata, pack_log2) == 60);
static_assert(std::is_standard_layout_v<pr_base_columns_metadata>);
static_assert(std::is_trivially_copyable_v<pr_base_columns_metadata>);

EXTERN __global__ void ab_pr_whir_accumulate_base_columns_kernel(const pr_base_columns_metadata m) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= (1u << (m.log_rows + m.pack_log2)))
    return;
  const u32 row = i & ((1u << m.log_rows) - 1u);
  const u32 y = i >> m.log_rows;
  const u32 pack = 1u << m.pack_log2;
  pr acc = pr::ZERO();
  u32 power_offset = 0;
#pragma unroll
  for (u32 source = 0; source < 2; source++) {
    for (u32 c = y; c < m.columns[source]; c += pack)
      acc = pr::fma(load<pr, ld_modifier::ca>(m.powers, power_offset + c / pack),
                    load<pr, ld_modifier::cs>(m.values[source], static_cast<u64>(c) * m.strides[source] + row), acc);
    power_offset += (m.columns[source] + pack - 1u) / pack;
  }
  store<pr, st_modifier::cs>(m.result, acc, i);
}

EXTERN __global__ void ab_pr_whir_eq_split_tables_kernel(const pr *point, u32 log_n, u32 low_bits, pr *lo, pr *hi) {
  const u32 bits = blockIdx.x == 0 ? low_bits : log_n - low_bits;
  const u32 offset = blockIdx.x == 0 ? 0 : low_bits;
  pr *out = blockIdx.x == 0 ? lo : hi;
  for (u32 i = threadIdx.x; i < (1u << bits); i += blockDim.x) {
    pr acc = pr::ONE();
    for (u32 b = 0; b < bits; b++) {
      const pr z = load<pr, ld_modifier::ca>(point, offset + b);
      acc = pr::mul(acc, (i >> b) & 1u ? z : pr::sub(pr::ONE(), z));
    }
    out[i] = acc;
  }
}

EXTERN __global__ void ab_pr_whir_eq_from_split_tables_kernel(const pr *lo, const pr *hi, u32 low_bits, u32 log_n, pr *eq) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= (1u << log_n))
    return;
  store<pr, st_modifier::cs>(eq, pr::mul(load<pr, ld_modifier::ca>(hi, i >> low_bits), load<pr, ld_modifier::ca>(lo, i & ((1u << low_bits) - 1u))), i);
}

EXTERN __global__ void ab_pr_whir_batched_opening_kernel(const pr *powers, const pr *claims, u32 count, pr *out) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  pr acc = pr::ZERO();
  for (u32 i = 0; i < count; i++)
    acc = pr::fma(powers[i], claims[i], acc);
  *out = acc;
}

} // namespace airbender::whir
