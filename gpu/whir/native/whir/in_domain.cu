#include "common.cuh"
#include "hash.cuh"
#include "ops/gkr_ops_helpers.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"
#include "whir_leaf_transform.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using ::airbender::ntt::params_inverse_power_source;
using ::airbender::ntt::whir_leaf_transform_params;

namespace airbender::whir {

// Symbolic in-domain query terms over natural-order coefficient leaves
// c[s] = P_s(rho^V). Per sumcheck step a term with weight w and point rho adds
//   h(X) = w * (1 - rho + X * (2 rho - 1)) * (E + X * O),
//   E = sum_j c[2j] * (rho^2)^j,   O = sum_j c[2j+1] * (rho^2)^j,
// to the three-point reductions [h(0), h(1), 4 h(1/2)]. A fold by alpha maps
// c[j] <- c[2j] + alpha * c[2j+1], w <- w * (1 - rho + alpha * (2 rho - 1)),
// rho <- rho^2. Exponents are u32 full-circle angles: index << (32 - log2 N).

constexpr unsigned WHIR_IN_DOMAIN_BLOCK_THREADS = 256;

EXTERN __global__ void ab_whir_in_domain_add_terms_kernel(const unsigned *indexes, const e4 *challenges, const unsigned query_domain_log2, const bf generator,
                                                          e4 *weights, bf *points, unsigned *exponents, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  const unsigned index = indexes[gid];
  weights[gid] = challenges[gid];
  points[gid] = bf::pow(generator, index);
  exponents[gid] = query_domain_log2 == 0 ? 0u : index << (32 - query_domain_log2);
}

EXTERN __global__ void ab_whir_in_domain_prepare_indexes_kernel(const unsigned *exponents, const unsigned domain_log2, const unsigned log_v, unsigned *indexes,
                                                                const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  const unsigned e = domain_log2 == 0 ? 0u : exponents[gid] >> (32 - domain_log2);
  const unsigned leaves_log2 = domain_log2 - log_v;
  const unsigned mask = leaves_log2 >= 32 ? 0xffffffffu : (1u << leaves_log2) - 1u;
  indexes[gid] = e & mask;
}

// Per-thread grid-stride accumulation of the terms' [h(0), h(1), 4 h(1/2)].
DEVICE_FORCEINLINE void accumulate_term_corrections(const e4 *leaves, const unsigned leaf_stride, const unsigned leaf_width, const e4 *weights,
                                                    const bf *points, const unsigned count, e4 &acc0, e4 &acc1, e4 &acc2) {
  const unsigned pairs = leaf_width >> 1;
  for (unsigned t = threadIdx.x; t < count; t += WHIR_IN_DOMAIN_BLOCK_THREADS) {
    const e4 *leaf = leaves + static_cast<size_t>(t) * leaf_stride;
    const bf rho = points[t];
    const bf rho_sqr = bf::sqr(rho);
    e4 even = leaf[2 * (pairs - 1)];
    e4 odd = leaf[2 * (pairs - 1) + 1];
    for (unsigned j = pairs - 1; j-- > 0;) {
      even = e4::fma(even, rho_sqr, leaf[2 * j]);
      odd = e4::fma(odd, rho_sqr, leaf[2 * j + 1]);
    }
    const e4 w = weights[t];
    acc0 = e4::add(acc0, e4::mul(e4::mul(w, bf::sub(bf::ONE(), rho)), even));
    acc1 = e4::add(acc1, e4::mul(e4::mul(w, rho), e4::add(even, odd)));
    acc2 = e4::add(acc2, e4::mul(w, e4::add(e4::dbl(even), odd)));
  }
}

// Block tree reduction of three E4 partials; the sums end in slot 0 of each
// array, visible to every thread after the last barrier.
DEVICE_FORCEINLINE void block_reduce_corrections(e4 *smem_p0, e4 *smem_p1, e4 *smem_p2, const e4 acc0, const e4 acc1, const e4 acc2) {
  const unsigned tid = threadIdx.x;
  smem_p0[tid] = acc0;
  smem_p1[tid] = acc1;
  smem_p2[tid] = acc2;
  __syncthreads();
#pragma unroll
  for (unsigned offset = WHIR_IN_DOMAIN_BLOCK_THREADS / 2; offset > 0; offset >>= 1) {
    if (tid < offset) {
      smem_p0[tid] = e4::add(smem_p0[tid], smem_p0[tid + offset]);
      smem_p1[tid] = e4::add(smem_p1[tid], smem_p1[tid + offset]);
      smem_p2[tid] = e4::add(smem_p2[tid], smem_p2[tid + offset]);
    }
    __syncthreads();
  }
}

// One term's fold by alpha: coefficient pairs, weight, point and angle.
DEVICE_FORCEINLINE void fold_term(e4 *leaf, const unsigned leaf_width, e4 &weight, bf &point, unsigned &exponent, const e4 alpha) {
  const unsigned pairs = leaf_width >> 1;
  for (unsigned j = 0; j < pairs; j++) {
    const e4 a = leaf[2 * j];
    const e4 b = leaf[2 * j + 1];
    leaf[j] = e4::fma(alpha, b, a);
  }
  const bf rho = point;
  const e4 eq = e4::fma(alpha, bf::sub(bf::dbl(rho), bf::ONE()), bf::sub(bf::ONE(), rho));
  weight = e4::mul(weight, eq);
  point = bf::sqr(rho);
  exponent <<= 1;
}

// Correct the three reductions, update the transcript on thread 0, then fold
// every term with the shared challenge. One block handles all active terms.
EXTERN __launch_bounds__(WHIR_IN_DOMAIN_BLOCK_THREADS) __global__
    void ab_whir_in_domain_correct_update_and_fold_kernel(e4 *leaves, const unsigned leaf_stride, const unsigned leaf_width, e4 *weights, bf *points,
                                                          unsigned *exponents, e4 *reductions, u32 *seed_io, e4 *coeffs_out, e4 *challenge_out,
                                                          const unsigned count) {
  __shared__ e4 smem_p0[WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ e4 smem_p1[WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ e4 smem_p2[WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ e4 smem_alpha;
  const unsigned tid = threadIdx.x;
  e4 acc0 = e4::ZERO();
  e4 acc1 = e4::ZERO();
  e4 acc2 = e4::ZERO();
  accumulate_term_corrections(leaves, leaf_stride, leaf_width, weights, points, count, acc0, acc1, acc2);
  block_reduce_corrections(smem_p0, smem_p1, smem_p2, acc0, acc1, acc2);
  if (tid == 0) {
    reductions[0] = e4::add(reductions[0], smem_p0[0]);
    reductions[1] = e4::add(reductions[1], smem_p1[0]);
    reductions[2] = e4::add(reductions[2], smem_p2[0]);
    ::airbender::gkr::ops::whir_fold_round_update_inline(reductions, seed_io, coeffs_out, challenge_out);
    smem_alpha = *challenge_out;
  }
  __syncthreads();
  const e4 alpha = smem_alpha;
  for (unsigned t = tid; t < count; t += WHIR_IN_DOMAIN_BLOCK_THREADS)
    fold_term(leaves + static_cast<size_t>(t) * leaf_stride, leaf_width, weights[t], points[t], exponents[t], alpha);
}

// Leaf-only refresh from a recomputed oracle's bit-reversed monomial copy
// (four BF limb columns of N, each bit-reversed over log N: coefficient u of
// slot polynomial P_s sits at offset bitrev_M(u) of block bitrev_V(s)). Tree
// index q decodes as in the residue query kernels; the leaf point satisfies
// x^V = omega_{M C}^coset * omega_M^row and slot s = P_s(x^V). One block per
// term: thread (r, s) accumulates u = r (mod R), R = 256 / V, with step y^R,
// then thread s combines sum_r y^r partial_r.
constexpr unsigned WHIR_IN_DOMAIN_LEAF_THREADS = 256;

EXTERN __launch_bounds__(WHIR_IN_DOMAIN_LEAF_THREADS) __global__
    void ab_whir_in_domain_leaves_from_monomials_kernel(const bf *coeffs, const whir_leaf_transform_params transform_params, const unsigned log_n,
                                                        const unsigned log_c, const unsigned log_v, const unsigned *tree_indexes, e4 *leaves,
                                                        const unsigned count) {
  __shared__ e4 partials[WHIR_IN_DOMAIN_LEAF_THREADS];
  const unsigned term = blockIdx.x;
  if (term >= count)
    return;
  const unsigned log_m = log_n - log_v;
  const unsigned m = 1u << log_m;
  const unsigned v = 1u << log_v;
  const unsigned n = 1u << log_n;
  const unsigned log_r = 8u - log_v;
  const unsigned r_count = 1u << log_r;
  const unsigned tid = threadIdx.x;
  const unsigned s = tid & (v - 1u);
  const unsigned r = tid >> log_v;

  const params_inverse_power_source inverse_powers{transform_params};
  const unsigned order = inverse_powers.params.omega_log_order;
  const unsigned exponent_mask = (1u << order) - 1u;
  const unsigned q = tree_indexes[term];
  const unsigned coset = bitreverse_low_bits(q >> log_m, log_c);
  const unsigned row = q & (m - 1u);
  const unsigned exponent = ((coset << (order - log_m - log_c)) + (row << (order - log_m))) & exponent_mask;
  const bf y = inverse_powers.get((0u - exponent) & exponent_mask);
  bf step = y;
  for (unsigned i = 0; i < log_r; i++)
    step = bf::sqr(step);

  e4 acc = e4::ZERO();
  if (r < m) {
    const bf *base = coeffs + (bitreverse_low_bits(s, log_v) << log_m);
    unsigned u = r + (((m - 1u - r) >> log_r) << log_r);
    while (true) {
      const unsigned offset = bitreverse_low_bits(u, log_m);
      bf limbs[4];
#pragma unroll
      for (unsigned l = 0; l < 4; l++)
        limbs[l] = load_ca(base + l * n + offset);
      acc = e4::fma(acc, step, e4(limbs));
      if (u == r)
        break;
      u -= r_count;
    }
  }
  partials[tid] = acc;
  __syncthreads();
  if (tid < v) {
    e4 value = e4::ZERO();
    for (unsigned j = r_count; j-- > 0;)
      value = e4::fma(value, y, partials[(j << log_v) + s]);
    leaves[(static_cast<size_t>(term) << log_v) + s] = value;
  }
}

} // namespace airbender::whir
