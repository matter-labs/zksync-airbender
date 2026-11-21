#pragma once
#include "common.cuh"

namespace airbender::whir::in_domain_detail {

template <typename F, typename P>
DEVICE_FORCEINLINE void add_terms(const unsigned *indexes, const F *challenges, const unsigned query_domain_log2, const P generator, F *weights, P *points,
                                  unsigned *exponents, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  const unsigned index = indexes[gid];
  weights[gid] = challenges[gid];
  points[gid] = P::pow(generator, index);
  exponents[gid] = query_domain_log2 == 0 ? 0u : index << (32 - query_domain_log2);
}

template <typename P, bool WITH_LEAF_POINTS>
DEVICE_FORCEINLINE void prepare_indexes(const unsigned *exponents, const P *points, const unsigned domain_log2, const unsigned log_v, unsigned *indexes,
                                        P *leaf_points, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  const unsigned e = domain_log2 == 0 ? 0u : exponents[gid] >> (32 - domain_log2);
  const unsigned leaves_log2 = domain_log2 - log_v;
  const unsigned mask = leaves_log2 >= 32 ? 0xffffffffu : (1u << leaves_log2) - 1u;
  indexes[gid] = e & mask;
  if constexpr (WITH_LEAF_POINTS) {
    P y = points[gid];
    for (unsigned i = 0; i < log_v; i++)
      y = P::sqr(y);
    leaf_points[gid] = y;
  }
}

template <typename F, typename P, unsigned BLOCK_THREADS>
DEVICE_FORCEINLINE void accumulate_term_corrections(const F *leaves, const unsigned leaf_stride, const unsigned leaf_width, const F *weights, const P *points,
                                                    const unsigned count, F &acc0, F &acc1, F &acc2) {
  const unsigned pairs = leaf_width >> 1;
  for (unsigned t = threadIdx.x; t < count; t += BLOCK_THREADS) {
    const F *leaf = leaves + static_cast<size_t>(t) * leaf_stride;
    const P rho = points[t];
    const P rho_sqr = P::sqr(rho);
    F even = leaf[2 * (pairs - 1)];
    F odd = leaf[2 * (pairs - 1) + 1];
    for (unsigned j = pairs - 1; j-- > 0;) {
      even = F::fma(even, rho_sqr, leaf[2 * j]);
      odd = F::fma(odd, rho_sqr, leaf[2 * j + 1]);
    }
    const F w = weights[t];
    acc0 = F::add(acc0, F::mul(F::mul(w, P::sub(P::ONE(), rho)), even));
    acc1 = F::add(acc1, F::mul(F::mul(w, rho), F::add(even, odd)));
    acc2 = F::add(acc2, F::mul(w, F::add(F::dbl(even), odd)));
  }
}

template <typename F, unsigned BLOCK_THREADS>
DEVICE_FORCEINLINE void block_reduce_corrections(F *smem_p0, F *smem_p1, F *smem_p2, const F acc0, const F acc1, const F acc2) {
  const unsigned tid = threadIdx.x;
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
}

template <typename F, typename P>
DEVICE_FORCEINLINE void fold_term(F *leaf, const unsigned leaf_width, F &weight, P &point, unsigned &exponent, const F alpha) {
  const unsigned pairs = leaf_width >> 1;
  for (unsigned j = 0; j < pairs; j++) {
    const F a = leaf[2 * j];
    const F b = leaf[2 * j + 1];
    leaf[j] = F::fma(alpha, b, a);
  }
  const P rho = point;
  const F eq = F::fma(alpha, P::sub(P::dbl(rho), P::ONE()), P::sub(P::ONE(), rho));
  weight = F::mul(weight, eq);
  point = P::sqr(rho);
  exponent <<= 1;
}

} // namespace airbender::whir::in_domain_detail
