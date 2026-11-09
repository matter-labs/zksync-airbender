#include "common.cuh"
#include "hash.cuh"
#include "in_domain_shared.cuh"
#include "ops/gkr_ops_helpers.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"
#include "whir_leaf_transform.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using ::airbender::ntt::params_inverse_power_source;
using ::airbender::ntt::whir_leaf_transform_params;

namespace airbender::whir {

using namespace in_domain_detail;

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
  add_terms(indexes, challenges, query_domain_log2, generator, weights, points, exponents, count);
}
EXTERN __global__ void ab_whir_in_domain_prepare_indexes_kernel(const unsigned *exponents, const unsigned domain_log2, const unsigned log_v, unsigned *indexes,
                                                                const unsigned count) {
  prepare_indexes<bf, false>(exponents, nullptr, domain_log2, log_v, indexes, nullptr, count);
}
// Per-thread grid-stride accumulation of the terms' [h(0), h(1), 4 h(1/2)].

// Block tree reduction of three E4 partials; the sums end in slot 0 of each
// array, visible to every thread after the last barrier.

// One term's fold by alpha: coefficient pairs, weight, point and angle.

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
  accumulate_term_corrections<e4, bf, WHIR_IN_DOMAIN_BLOCK_THREADS>(leaves, leaf_stride, leaf_width, weights, points, count, acc0, acc1, acc2);
  block_reduce_corrections<e4, WHIR_IN_DOMAIN_BLOCK_THREADS>(smem_p0, smem_p1, smem_p2, acc0, acc1, acc2);
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

// The fused kernel above split around the challenge for a PoW-gated folding
// draw: correct the reductions and commit the round polynomial here, draw the
// challenge on the stream, then fold the terms with it below.
EXTERN __launch_bounds__(WHIR_IN_DOMAIN_BLOCK_THREADS) __global__
    void ab_whir_in_domain_correct_and_commit_kernel(const e4 *leaves, const unsigned leaf_stride, const unsigned leaf_width, const e4 *weights,
                                                     const bf *points, e4 *reductions, u32 *seed_io, e4 *coeffs_out, const unsigned count) {
  __shared__ e4 smem_p0[WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ e4 smem_p1[WHIR_IN_DOMAIN_BLOCK_THREADS];
  __shared__ e4 smem_p2[WHIR_IN_DOMAIN_BLOCK_THREADS];
  e4 acc0 = e4::ZERO();
  e4 acc1 = e4::ZERO();
  e4 acc2 = e4::ZERO();
  accumulate_term_corrections<e4, bf, WHIR_IN_DOMAIN_BLOCK_THREADS>(leaves, leaf_stride, leaf_width, weights, points, count, acc0, acc1, acc2);
  block_reduce_corrections<e4, WHIR_IN_DOMAIN_BLOCK_THREADS>(smem_p0, smem_p1, smem_p2, acc0, acc1, acc2);
  if (threadIdx.x == 0) {
    reductions[0] = e4::add(reductions[0], smem_p0[0]);
    reductions[1] = e4::add(reductions[1], smem_p1[0]);
    reductions[2] = e4::add(reductions[2], smem_p2[0]);
    u32 state[::airbender::hash::STATE_SIZE];
    ::airbender::gkr::ops::whir_fold_round_commit_inline(reductions, seed_io, coeffs_out, state);
  }
}

// Fold every term by the device-resident challenge; one thread per term.
EXTERN __global__ void ab_whir_in_domain_fold_terms_kernel(e4 *leaves, const unsigned leaf_stride, const unsigned leaf_width, e4 *weights, bf *points,
                                                           unsigned *exponents, const e4 *challenge, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  fold_term(leaves + static_cast<size_t>(gid) * leaf_stride, leaf_width, weights[gid], points[gid], exponents[gid], *challenge);
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
