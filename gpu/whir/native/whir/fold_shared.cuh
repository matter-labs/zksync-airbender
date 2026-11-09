#pragma once

#include "common.cuh"
#include "primitives/memory.cuh"

namespace airbender::whir::whir_detail {

using namespace ::airbender::primitives::memory;

template <class F> struct flat_coefficients {
  const F *ptr;
  DEVICE_FORCEINLINE F get_at_row(int row) const { return load<F, ld_modifier::cs>(ptr, row); }
  DEVICE_FORCEINLINE void add_row(int row) { ptr += row; }
};

template <class F, bool EVALUATION_FORM> DEVICE_FORCEINLINE void fold_adjacent(const F *src, F *dst, const F *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const F a = load<F, ld_modifier::cs>(src, 2 * gid);
  const F b = load<F, ld_modifier::cs>(src, 2 * gid + 1);
  F diff;
  if constexpr (EVALUATION_FORM)
    diff = F::sub(b, a);
  else
    diff = b;
  const F folded = F::fma(*challenge, diff, a);
  store<F, st_modifier::cs>(dst, folded, gid);
}

template <class F, unsigned BLOCK_THREADS = 256>
DEVICE_FORCEINLINE void fold_adjacent_pair(const F *src_a, F *dst_a, const F *src_b, F *dst_b, const F *challenge, const unsigned half_len) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= half_len)
    return;

  const F c = *challenge;
  const F a_even = load<F, ld_modifier::cs>(src_a, 2 * gid);
  const F a_odd = load<F, ld_modifier::cs>(src_a, 2 * gid + 1);
  store<F, st_modifier::cs>(dst_a, F::fma(c, F::sub(a_odd, a_even), a_even), gid);
  const F b_even = load<F, ld_modifier::cs>(src_b, 2 * gid);
  const F b_odd = load<F, ld_modifier::cs>(src_b, 2 * gid + 1);
  store<F, st_modifier::cs>(dst_b, F::fma(c, F::sub(b_odd, b_even), b_even), gid);
}

template <class F, unsigned BLOCK_THREADS = 256>
DEVICE_FORCEINLINE void three_point_partials(const F *__restrict__ eval, const F *__restrict__ eq, F *__restrict__ partials, const unsigned half,
                                             F *__restrict__ smem_p0, F *__restrict__ smem_p1, F *__restrict__ smem_p2) {

  const unsigned tid = threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;

  F acc0 = F::ZERO();
  F acc1 = F::ZERO();
  F acc2 = F::ZERO();

  for (unsigned i = blockIdx.x * blockDim.x + tid; i < half; i += stride) {
    const F ev_even = load<F, ld_modifier::cs>(eval, 2 * i);
    const F ev_odd = load<F, ld_modifier::cs>(eval, 2 * i + 1);
    const F eq_even = load<F, ld_modifier::cs>(eq, 2 * i);
    const F eq_odd = load<F, ld_modifier::cs>(eq, 2 * i + 1);
    acc0 = F::add(acc0, F::mul(ev_even, eq_even));
    acc1 = F::add(acc1, F::mul(ev_odd, eq_odd));
    acc2 = F::add(acc2, F::mul(F::add(ev_even, ev_odd), F::add(eq_even, eq_odd)));
  }

  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = F::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = F::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = F::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    partials[blockIdx.x * 3u + 0u] = smem_p0[0];
    partials[blockIdx.x * 3u + 1u] = smem_p1[0];
    partials[blockIdx.x * 3u + 2u] = smem_p2[0];
  }
}

template <class F, unsigned BLOCK_THREADS = 256>
DEVICE_FORCEINLINE void three_point_finalize(const F *__restrict__ partials, const unsigned num_blocks, F *__restrict__ reduce_out, F *__restrict__ smem_p0,
                                             F *__restrict__ smem_p1, F *__restrict__ smem_p2) {

  const unsigned tid = threadIdx.x;

  F acc0 = F::ZERO();
  F acc1 = F::ZERO();
  F acc2 = F::ZERO();
  for (unsigned b = tid; b < num_blocks; b += BLOCK_THREADS) {
    acc0 = F::add(acc0, partials[b * 3u + 0u]);
    acc1 = F::add(acc1, partials[b * 3u + 1u]);
    acc2 = F::add(acc2, partials[b * 3u + 2u]);
  }

  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = F::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = F::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = F::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    reduce_out[0] = smem_p0[0];
    reduce_out[1] = smem_p1[0];
    reduce_out[2] = smem_p2[0];
  }
}

template <class F, unsigned BLOCK_THREADS = 256>
DEVICE_FORCEINLINE void three_point_combined(const F *__restrict__ eval, const F *__restrict__ eq, F *__restrict__ reduce_out, const unsigned half,
                                             F *__restrict__ smem_p0, F *__restrict__ smem_p1, F *__restrict__ smem_p2) {

  const unsigned tid = threadIdx.x;

  F acc0 = F::ZERO();
  F acc1 = F::ZERO();
  F acc2 = F::ZERO();
  if (tid < half) {
    const F ev_lo = load<F, ld_modifier::cs>(eval, 2 * tid);
    const F ev_hi = load<F, ld_modifier::cs>(eval, 2 * tid + 1);
    const F eq_lo = load<F, ld_modifier::cs>(eq, 2 * tid);
    const F eq_hi = load<F, ld_modifier::cs>(eq, 2 * tid + 1);
    acc0 = F::mul(ev_lo, eq_lo);
    acc1 = F::mul(ev_hi, eq_hi);
    acc2 = F::mul(F::add(ev_lo, ev_hi), F::add(eq_lo, eq_hi));
  }
  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();

#pragma unroll
  for (unsigned offset = BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = F::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = F::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = F::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }

  if (tid == 0) {
    reduce_out[0] = smem_p0[0];
    reduce_out[1] = smem_p1[0];
    reduce_out[2] = smem_p2[0];
  }
}

template <class F, unsigned BLOCK_THREADS = 256>
DEVICE_FORCEINLINE void sum(const F *__restrict__ values, const unsigned count, F *__restrict__ out, F *__restrict__ smem) {

  const unsigned tid = threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;

  F acc = F::ZERO();
  for (unsigned i = blockIdx.x * blockDim.x + tid; i < count; i += stride)
    acc = F::add(acc, load<F, ld_modifier::cs>(values, i));

  smem[tid] = acc;
  __syncthreads();

#pragma unroll
  for (unsigned offset = BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset)
      smem[tid] = F::add(smem[tid], smem[tid + offset]);
    __syncthreads();
  }

  if (tid == 0)
    out[blockIdx.x] = smem[0];
}

template <class F, class Source> DEVICE_FORCEINLINE void evaluate_monomial_small(Source src, F *dst, const F z, const unsigned log_count) {
  const int count = 1 << log_count;
  const int gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;

  F result{src.get_at_row(gid)};
  const F adjustment = F::pow(z, gid);
  dst[gid] = F::mul(result, adjustment);
}

template <class F, class Source> DEVICE_FORCEINLINE void evaluate_monomial(Source src, F *dst, const F z, const F z_stride, const unsigned log_count) {
  constexpr int VALS_PER_THREAD = 32;

  const int count = 1 << log_count;
  const int gid = blockIdx.x * blockDim.x + threadIdx.x;
  const int gmem_stride = gridDim.x * blockDim.x;
  if (gid >= count / VALS_PER_THREAD)
    return;

  src.add_row(gid);

  // Horner rule works backwards from highest powers
  F result{src.get_at_row(gmem_stride * (VALS_PER_THREAD - 1))};
#pragma unroll
  for (int k{VALS_PER_THREAD - 2}; k >= 0; k--) {
    result = F::mul(result, z_stride);
    result = F::add(result, src.get_at_row(gmem_stride * k));
  }

  const F adjustment = F::pow(z, gid);
  dst[gid] = F::mul(result, adjustment);
}

} // namespace airbender::whir::whir_detail
