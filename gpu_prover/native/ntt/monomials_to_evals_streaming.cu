#include "ntt.cuh"

// Streaming multi-coset single-column NTT for log_n in [3, 8].
//
// Each block owns a contiguous run of cosets and iterates over them with a
// running shift update m'_{c+Delta}[r] = m'_c[r] * D[r], where
// D[r] = omega^(Delta * bitrev(r)) is loop-invariant for the launch.
// Setup (initial monomial load, coset shift, D[r] precompute) happens once per
// block and amortizes across many iterations.
//
// Per-thread state: 8 cells of monomial-prime in registers, 8 cells of D[r] in
// registers, 8 cells working scratch during butterflies. Cross-thread stages
// use __shfl_xor_sync within a TPC-lane subwarp (TPC = 2^(log_n - 3)). Butterfly
// twiddles live in smem with stage-major layout so each thread reads its own
// bank cell every stage; cosets sharing a warp broadcast across lanes.
//
// Output is contiguous coset-major: out[coset * coset_stride_bf + row] for
// row in [0, N). The caller positions `out` at coset 0 of one column; multi-
// column workloads launch the kernel once per column.

namespace airbender::ntt {

struct __align__(32) bf8 {
  bf values[8];
};

// On sm_90+ the launch bounds cap registers at 64 per thread (BLK * LB = 1024 =>
// reg_cap = 65536 / 1024 = 64), which is enough for the kernel without spilling.
// Older arches (sm_8x) need ~80 registers, so we let ptxas pick there.
#if defined(__CUDA_ARCH__) && __CUDA_ARCH__ >= 900
#define NTT_STREAMING_LAUNCH_BOUNDS(BLK) __launch_bounds__(BLK, (1024 + (BLK) - 1) / (BLK))
#else
#define NTT_STREAMING_LAUNCH_BOUNDS(BLK)
#endif

template <int LOG_N, int BLK>
DEVICE_FORCEINLINE void monomials_to_evals_streaming_impl(const bf *__restrict__ monomials, bf *__restrict__ out, const int coset_index_base,
                                                          const int coset_factor_shift, const unsigned num_cosets, const size_t coset_stride_bf) {
  static_assert(LOG_N >= 3 && LOG_N <= 8, "streaming NTT supports log_n in [3, 8]");
  constexpr int LOG_VPT = 3;
  constexpr int VPT = 1 << LOG_VPT;
  constexpr int N = 1 << LOG_N;
  constexpr int LOG_TPC = LOG_N - LOG_VPT;
  constexpr int TPC = 1 << LOG_TPC;
  constexpr int COSETS_PER_IT = BLK / TPC;
  constexpr unsigned BS = OMEGA_LOG_ORDER - LOG_N;
  static_assert(BLK % TPC == 0, "BLK must be a multiple of TPC");

  // Smem twiddle layout: stage-major, thread-position bank-cell within each stage.
  //   stage 0: 4 cells per thread (4 within-thread butterflies)
  //   stage 1: 2 cells per thread
  //   stage 2: 1 cell per thread (skipped at LOG_N=3 — last stage has no twiddle)
  //   cross-thread stages 3..LOG_N-2 (non-last only): 1 cell per thread each
  constexpr int CROSS_TW_STAGES = (LOG_N >= 5) ? (LOG_N - 4) : 0;
  constexpr int STAGE2_TW = (LOG_N >= 4) ? 1 : 0;
  constexpr int S0_OFF = 0;
  constexpr int S1_OFF = S0_OFF + 4 * TPC;
  constexpr int S2_OFF = S1_OFF + 2 * TPC;
  constexpr int CROSS_OFF = S2_OFF + STAGE2_TW * TPC;
  constexpr int TW_CELLS = CROSS_OFF + CROSS_TW_STAGES * TPC;
  __shared__ bf smem_tw[TW_CELLS];

  const unsigned tid = threadIdx.x;
  const unsigned thread_pos = tid & (TPC - 1);
  const unsigned coset_in_it = tid >> LOG_TPC;
  const unsigned K_shift = static_cast<unsigned>(coset_factor_shift);

  // Persistent grid: each block takes a slice of total_iters and walks it
  // sequentially. Block 0 takes the first chunk, block 1 the next, etc., with
  // a one-iter remainder distributed to the first `extra` blocks.
  const unsigned total_iters = num_cosets / static_cast<unsigned>(COSETS_PER_IT);
  const unsigned base = total_iters / gridDim.x;
  const unsigned extra = total_iters - base * gridDim.x;
  const unsigned b = blockIdx.x;
  const unsigned iters = base + (b < extra ? 1u : 0u);
  const unsigned iter_start = base * b + (b < extra ? b : extra);
  const unsigned block_base = iter_start * static_cast<unsigned>(COSETS_PER_IT);

  // Init smem twiddles: each thread writes only the cells it will read later,
  // so no __syncthreads is needed.
  {
    const unsigned tp = thread_pos;
    smem_tw[S0_OFF + 0 * TPC + tp] = get_forward_twiddle_power(bitrev(tp * 4u + 0u, LOG_N - 1) << BS);
    smem_tw[S0_OFF + 1 * TPC + tp] = get_forward_twiddle_power(bitrev(tp * 4u + 1u, LOG_N - 1) << BS);
    smem_tw[S0_OFF + 2 * TPC + tp] = get_forward_twiddle_power(bitrev(tp * 4u + 2u, LOG_N - 1) << BS);
    smem_tw[S0_OFF + 3 * TPC + tp] = get_forward_twiddle_power(bitrev(tp * 4u + 3u, LOG_N - 1) << BS);
    smem_tw[S1_OFF + 0 * TPC + tp] = get_forward_twiddle_power(bitrev(tp * 2u + 0u, LOG_N - 1) << BS);
    smem_tw[S1_OFF + 1 * TPC + tp] = get_forward_twiddle_power(bitrev(tp * 2u + 1u, LOG_N - 1) << BS);
    if constexpr (LOG_N >= 4) {
      smem_tw[S2_OFF + tp] = get_forward_twiddle_power(bitrev(tp, LOG_N - 1) << BS);
    }
    if constexpr (CROSS_TW_STAGES > 0) {
#pragma unroll
      for (int cs = 0; cs < CROSS_TW_STAGES; ++cs) {
        const int s = 3 + cs;
        const unsigned mask_lanes = 1u << cs;
        const unsigned left_tp = tp & ~mask_lanes;
        const unsigned group = (left_tp * static_cast<unsigned>(VPT)) >> (s + 1);
        smem_tw[CROSS_OFF + cs * TPC + tp] = get_forward_twiddle_power(bitrev(group, LOG_N - 1) << BS);
      }
    }
  }

  // bitrev_N(row) where row = (tp << LOG_VPT) | r.
  // bitrev_3({0..7}) = {0,4,2,6,1,5,3,7}, then shifted by LOG_TPC; tp's bitrev
  // contributes the low bits.
  constexpr unsigned ROW_BREV3[8] = {0u, 4u, 2u, 6u, 1u, 5u, 3u, 7u};
  const unsigned tp_brev = (LOG_TPC > 0) ? bitrev(thread_pos, LOG_TPC) : 0u;
  unsigned bitrev_row[8];
#pragma unroll
  for (int r = 0; r < 8; ++r)
    bitrev_row[r] = (ROW_BREV3[r] << LOG_TPC) | tp_brev;

  // Setup: load this thread's 8 monomials, fold in initial coset shift, and
  // precompute the per-row delta twiddle D[r] = omega^(Delta * bitrev(r)) where
  // Delta = COSETS_PER_IT << K_shift is the absolute step in coset-factor space.
  const unsigned c_rel = block_base + coset_in_it;
  const unsigned c_abs = static_cast<unsigned>(coset_index_base) + c_rel;
  const unsigned cfp0 = c_abs << K_shift;

  bf m_prime[8];
#pragma unroll
  for (int r = 0; r < 8; ++r) {
    const unsigned row = (thread_pos << LOG_VPT) | static_cast<unsigned>(r);
    bf m = load_ca(monomials + row);
    if (bitrev_row[r] != 0u) {
      m = bf::mul(m, get_forward_twiddle_power(bitrev_row[r] * cfp0));
    }
    m_prime[r] = m;
  }

  const unsigned delta_cfp = static_cast<unsigned>(COSETS_PER_IT) << K_shift;
  bf D[8];
#pragma unroll
  for (int r = 0; r < 8; ++r) {
    D[r] = (bitrev_row[r] == 0u) ? bf::ONE() : get_forward_twiddle_power(bitrev_row[r] * delta_cfp);
  }

  // shfl_xor mask: for log_n < 8 the cross-thread partners are within a
  // TPC-lane subwarp; pass only those lanes in the active mask.
  const unsigned lane = tid & 31u;
  constexpr unsigned LANE_GROUP_MASK = (TPC >= 32) ? 0xFFFFFFFFu : ((1u << TPC) - 1u);
  const unsigned subwarp_mask = (TPC >= 32) ? 0xFFFFFFFFu : (LANE_GROUP_MASK << ((lane >> LOG_TPC) * TPC));

  for (unsigned it = 0; it < iters; ++it) {
    bf w0 = m_prime[0], w1 = m_prime[1], w2 = m_prime[2], w3 = m_prime[3];
    bf w4 = m_prime[4], w5 = m_prime[5], w6 = m_prime[6], w7 = m_prime[7];

    // Stage 0: pair distance 1 (within-thread).
    {
      const bf t0 = smem_tw[S0_OFF + 0 * TPC + thread_pos];
      const bf t1 = smem_tw[S0_OFF + 1 * TPC + thread_pos];
      const bf t2 = smem_tw[S0_OFF + 2 * TPC + thread_pos];
      const bf t3 = smem_tw[S0_OFF + 3 * TPC + thread_pos];
      bf s, d;
      s = bf::add(w0, w1);
      d = bf::sub(w0, w1);
      w0 = s;
      w1 = bf::mul(d, t0);
      s = bf::add(w2, w3);
      d = bf::sub(w2, w3);
      w2 = s;
      w3 = bf::mul(d, t1);
      s = bf::add(w4, w5);
      d = bf::sub(w4, w5);
      w4 = s;
      w5 = bf::mul(d, t2);
      s = bf::add(w6, w7);
      d = bf::sub(w6, w7);
      w6 = s;
      w7 = bf::mul(d, t3);
    }

    // Stage 1: pair distance 2 (within-thread).
    {
      const bf t0 = smem_tw[S1_OFF + 0 * TPC + thread_pos];
      const bf t1 = smem_tw[S1_OFF + 1 * TPC + thread_pos];
      bf s, d;
      s = bf::add(w0, w2);
      d = bf::sub(w0, w2);
      w0 = s;
      w2 = bf::mul(d, t0);
      s = bf::add(w1, w3);
      d = bf::sub(w1, w3);
      w1 = s;
      w3 = bf::mul(d, t0);
      s = bf::add(w4, w6);
      d = bf::sub(w4, w6);
      w4 = s;
      w6 = bf::mul(d, t1);
      s = bf::add(w5, w7);
      d = bf::sub(w5, w7);
      w5 = s;
      w7 = bf::mul(d, t1);
    }

    // Stage 2: pair distance 4 (within-thread). For LOG_N=3 this is the last
    // stage and skips the twiddle.
    {
      bf s, d;
      if constexpr (LOG_N >= 4) {
        const bf t = smem_tw[S2_OFF + thread_pos];
        s = bf::add(w0, w4);
        d = bf::sub(w0, w4);
        w0 = s;
        w4 = bf::mul(d, t);
        s = bf::add(w1, w5);
        d = bf::sub(w1, w5);
        w1 = s;
        w5 = bf::mul(d, t);
        s = bf::add(w2, w6);
        d = bf::sub(w2, w6);
        w2 = s;
        w6 = bf::mul(d, t);
        s = bf::add(w3, w7);
        d = bf::sub(w3, w7);
        w3 = s;
        w7 = bf::mul(d, t);
      } else {
        s = bf::add(w0, w4);
        d = bf::sub(w0, w4);
        w0 = s;
        w4 = d;
        s = bf::add(w1, w5);
        d = bf::sub(w1, w5);
        w1 = s;
        w5 = d;
        s = bf::add(w2, w6);
        d = bf::sub(w2, w6);
        w2 = s;
        w6 = d;
        s = bf::add(w3, w7);
        d = bf::sub(w3, w7);
        w3 = s;
        w7 = d;
      }
    }

// Cross-thread stages s = 3..LOG_N-1 via shfl_xor with mask = 2^(s-3). The
// final stage skips the twiddle multiplication.
#define NTT_CROSS_STAGE(STAGE)                                                                                                                                 \
  do {                                                                                                                                                         \
    constexpr int s = (STAGE);                                                                                                                                 \
    constexpr int cs = s - 3;                                                                                                                                  \
    constexpr unsigned mask_lanes = 1u << cs;                                                                                                                  \
    constexpr bool is_last = (s == LOG_N - 1);                                                                                                                 \
    const bool is_lo = (thread_pos & mask_lanes) == 0u;                                                                                                        \
    bf t;                                                                                                                                                      \
    if constexpr (!is_last)                                                                                                                                    \
      t = smem_tw[CROSS_OFF + cs * TPC + thread_pos];                                                                                                          \
    const unsigned q0 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w0), mask_lanes);                                                                       \
    const unsigned q1 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w1), mask_lanes);                                                                       \
    const unsigned q2 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w2), mask_lanes);                                                                       \
    const unsigned q3 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w3), mask_lanes);                                                                       \
    const unsigned q4 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w4), mask_lanes);                                                                       \
    const unsigned q5 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w5), mask_lanes);                                                                       \
    const unsigned q6 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w6), mask_lanes);                                                                       \
    const unsigned q7 = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w7), mask_lanes);                                                                       \
    auto apply = [&](bf &W, unsigned Q) {                                                                                                                      \
      const bf pv = bf::from_reduced_raw_repr(Q);                                                                                                              \
      const bf l = is_lo ? W : pv;                                                                                                                             \
      const bf r = is_lo ? pv : W;                                                                                                                             \
      if constexpr (is_last) {                                                                                                                                 \
        W = is_lo ? bf::add(l, r) : bf::sub(l, r);                                                                                                             \
      } else {                                                                                                                                                 \
        W = is_lo ? bf::add(l, r) : bf::mul(bf::sub(l, r), t);                                                                                                 \
      }                                                                                                                                                        \
    };                                                                                                                                                         \
    apply(w0, q0);                                                                                                                                             \
    apply(w1, q1);                                                                                                                                             \
    apply(w2, q2);                                                                                                                                             \
    apply(w3, q3);                                                                                                                                             \
    apply(w4, q4);                                                                                                                                             \
    apply(w5, q5);                                                                                                                                             \
    apply(w6, q6);                                                                                                                                             \
    apply(w7, q7);                                                                                                                                             \
  } while (0)

    if constexpr (LOG_N >= 4) {
      NTT_CROSS_STAGE(3);
    }
    if constexpr (LOG_N >= 5) {
      NTT_CROSS_STAGE(4);
    }
    if constexpr (LOG_N >= 6) {
      NTT_CROSS_STAGE(5);
    }
    if constexpr (LOG_N >= 7) {
      NTT_CROSS_STAGE(6);
    }
    if constexpr (LOG_N >= 8) {
      NTT_CROSS_STAGE(7);
    }
#undef NTT_CROSS_STAGE

    // Vec8 (32 B aligned) store via load_unit<bf8>::type = u32x8 on sm_100+ →
    // STG.E.ENL2.256; older arches fall back to two STG.E.128 ops in PTX.
    const unsigned coset_rel = block_base + it * static_cast<unsigned>(COSETS_PER_IT) + coset_in_it;
    bf *coset_ptr = out + static_cast<size_t>(coset_rel) * coset_stride_bf + (thread_pos << LOG_VPT);
    bf8 packed;
    packed.values[0] = w0;
    packed.values[1] = w1;
    packed.values[2] = w2;
    packed.values[3] = w3;
    packed.values[4] = w4;
    packed.values[5] = w5;
    packed.values[6] = w6;
    packed.values[7] = w7;
    store_cs(reinterpret_cast<bf8 *>(coset_ptr), packed);

    // Running shift update m'[r] *= D[r] — advances to the next iter's coset.
    m_prime[0] = bf::mul(m_prime[0], D[0]);
    m_prime[1] = bf::mul(m_prime[1], D[1]);
    m_prime[2] = bf::mul(m_prime[2], D[2]);
    m_prime[3] = bf::mul(m_prime[3], D[3]);
    m_prime[4] = bf::mul(m_prime[4], D[4]);
    m_prime[5] = bf::mul(m_prime[5], D[5]);
    m_prime[6] = bf::mul(m_prime[6], D[6]);
    m_prime[7] = bf::mul(m_prime[7], D[7]);
  }
}

#define DEFINE_STREAMING_KERNEL(LOG_N, BLK)                                                                                                                    \
  EXTERN NTT_STREAMING_LAUNCH_BOUNDS(BLK)                                                                                                                      \
  __global__ void ab_monomials_to_evals_streaming_##LOG_N##_stages_kernel(const bf *__restrict__ monomials, bf *__restrict__ out, const int coset_index_base,  \
                                                                          const int coset_factor_shift, const unsigned num_cosets,                             \
                                                                          const unsigned long long coset_stride_bf) {                                          \
    monomials_to_evals_streaming_impl<LOG_N, BLK>(monomials, out, coset_index_base, coset_factor_shift, num_cosets, static_cast<size_t>(coset_stride_bf));     \
  }

DEFINE_STREAMING_KERNEL(3, 256)
DEFINE_STREAMING_KERNEL(4, 256)
DEFINE_STREAMING_KERNEL(5, 256)
DEFINE_STREAMING_KERNEL(6, 256)
DEFINE_STREAMING_KERNEL(7, 256)
DEFINE_STREAMING_KERNEL(8, 256)

#undef DEFINE_STREAMING_KERNEL
#undef NTT_STREAMING_LAUNCH_BOUNDS

} // namespace airbender::ntt
