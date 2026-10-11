#include "context.cuh"

namespace airbender::ntt {

struct pr_eq_sample {
  pr point;
  pr weight;
};
static_assert(sizeof(pr_eq_sample) == 32);
static_assert(alignof(pr_eq_sample) == 16);
static_assert(offsetof(pr_eq_sample, point) == 0);
static_assert(offsetof(pr_eq_sample, weight) == 16);
static_assert(std::is_standard_layout_v<pr_eq_sample>);
static_assert(std::is_trivially_copyable_v<pr_eq_sample>);

DEVICE_FORCEINLINE pr pr_eq_factor(pr point, const u32 first_bit, const u32 bits, const u32 index) {
  pr factor = pr::ONE();
  for (u32 bit = 0; bit < first_bit + bits; bit++) {
    if (bit >= first_bit) {
      const pr value = (index >> (bit - first_bit)) & 1u ? point : pr::sub(pr::ONE(), point);
      factor = pr::mul(factor, value);
    }
    point = pr::sqr(point);
  }
  return factor;
}

EXTERN __launch_bounds__(256) __global__ void ab_pr_update_eq_poly_kernel(pr *eq, const u32 log_n, const pr_eq_sample *samples, const u32 count) {
  const u32 rows = 1u << log_n;
  const u32 lo_bits = min(8u, log_n);
  const u32 mid_bits = min(4u, log_n - lo_bits);
  const u32 hi_bits = log_n - lo_bits - mid_bits;
  const u32 t = threadIdx.x;
  const u32 first_row = blockIdx.x * 4096 + t;
  __shared__ pr mid[16];
  __shared__ pr high_weight;
  pr values[16];
#pragma unroll
  for (u32 j = 0; j < 16; j++) {
    const u32 row = first_row + j * 256;
    values[j] = row < rows ? load_cg(eq + row) : pr::ZERO();
  }
  for (u32 sample_idx = 0; sample_idx < count; sample_idx++) {
    const pr point = load_ca(&samples[sample_idx].point);
    if (t == 0)
      high_weight = pr::mul(load_ca(&samples[sample_idx].weight), pr_eq_factor(point, lo_bits + mid_bits, hi_bits, blockIdx.x));
    if (t < (1u << mid_bits))
      mid[t] = pr_eq_factor(point, lo_bits, mid_bits, t);
    __syncthreads();
    const pr low = pr_eq_factor(point, 0, lo_bits, t);
    const pr weighted_low = pr::mul(high_weight, low);
#pragma unroll
    for (u32 j = 0; j < 16; j++) {
      const u32 row = first_row + j * 256;
      if (row < rows)
        values[j] = pr::add(values[j], pr::mul(weighted_low, mid[j]));
    }
    __syncthreads();
  }
#pragma unroll
  for (u32 j = 0; j < 16; j++) {
    const u32 row = first_row + j * 256;
    if (row < rows)
      store_cg(eq + row, values[j]);
  }
}

} // namespace airbender::ntt
