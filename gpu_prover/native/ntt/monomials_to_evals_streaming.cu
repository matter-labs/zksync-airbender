#include "ntt.cuh"

// Streaming multi-coset single-column NTT for log_n in [2, 8].
//
// Each block owns a contiguous run of cosets and iterates over them with a
// running shift update m'_{c+Delta}[r] = m'_c[r] * D[r], where
// D[r] = omega^(Delta * bitrev(r)) is loop-invariant for the launch.
// Setup (initial monomial load, coset shift, D[r] precompute) happens once per
// block and amortizes across many iterations.
//
// Two VPT variants are emitted:
//   - VPT=4 (LOG_VPT=2, log_n in [2, 7]): 4 values/thread, 16 B aligned bf4
//     store -> STG.E.128. Lower register pressure (32 regs/thread vs 64),
//     higher occupancy (8 blocks/SM vs 4). This is the default for log_n
//     <= 7 across all architectures: a 500-iter Blackwell sweep showed v4
//     ≥ v8 across the range (tied at DRAM saturation for log_n in [2, 6],
//     v4 ~4% faster at log_n=7), and on sm_<90 v8's STG.E.256 decomposes
//     into two 128-bit transactions, wiping out coalescing.
//   - VPT=8 (LOG_VPT=3, log_n=8): 8 values/thread, 32 B aligned bf8 store.
//     Required for log_n=8 because VPT=4 would need TPC=64 threads/coset,
//     exceeding a warp; the last cross-thread stage's __shfl_xor_sync
//     can't reach across the warp boundary. On sm_100+ this fuses to
//     STG.E.ENL2.256; on older arch it emits two STG.E.128.
//
// Per-thread state: VPT cells of monomial-prime in registers, VPT cells of
// D[r] in registers, VPT cells working scratch during butterflies. Cross-thread
// stages use __shfl_xor_sync within a TPC-lane subwarp (TPC = N / VPT).
// Butterfly twiddles live in smem with stage-major layout so each thread reads
// its own bank cell every stage; cosets sharing a warp broadcast across lanes.
//
// Output is contiguous coset-major: out[coset * coset_stride_bf + row] for
// row in [0, N). The caller positions `out` at coset 0 of one column; multi-
// column workloads launch the kernel once per column.

namespace airbender::ntt {

struct __align__(16) bf4 {
  bf values[4];
};

struct __align__(32) bf8 {
  bf values[8];
};

template <int VPT> struct bf_vec;
template <> struct bf_vec<4> {
  using type = bf4;
};
template <> struct bf_vec<8> {
  using type = bf8;
};

// VPT=8 launch_bounds: gated on __CUDA_ARCH__ >= 900 because older archs need
// ~80 regs/thread without the cap; the 64-reg cap implied by (1024+BLK-1)/BLK
// would spill. The Rust dispatcher only routes log_n=8 here on sm_<90, so the
// older-arch path runs that single size with ptxas's natural choice.
#if defined(__CUDA_ARCH__) && __CUDA_ARCH__ >= 900
#define NTT_STREAMING_LAUNCH_BOUNDS_V8(BLK) __launch_bounds__(BLK, (1024 + (BLK) - 1) / (BLK))
#else
#define NTT_STREAMING_LAUNCH_BOUNDS_V8(BLK)
#endif

// VPT=4 launch_bounds: half the per-thread state of VPT=8 → target 8 blocks/SM
// (cap ≈ 32 regs/thread on a 65 K-reg SM). Applied uniformly across archs.
#define NTT_STREAMING_LAUNCH_BOUNDS_V4(BLK) __launch_bounds__(BLK, (2048 + (BLK) - 1) / (BLK))

template <int LOG_N, int LOG_VPT, int BLK>
DEVICE_FORCEINLINE void monomials_to_evals_streaming_impl(const bf *__restrict__ monomials, bf *__restrict__ out, const int coset_index_base,
                                                          const int coset_factor_shift, const unsigned num_cosets, const size_t coset_stride_bf) {
  static_assert(LOG_N >= 2 && LOG_N <= 8, "streaming NTT supports log_n in [2, 8]");
  static_assert(LOG_VPT == 2 || LOG_VPT == 3, "streaming NTT supports LOG_VPT in {2, 3} (VPT in {4, 8})");
  static_assert(LOG_N >= LOG_VPT, "LOG_N must be >= LOG_VPT");
  constexpr int VPT = 1 << LOG_VPT;
  constexpr int N = 1 << LOG_N;
  (void)N;
  constexpr int LOG_TPC = LOG_N - LOG_VPT;
  constexpr int TPC = 1 << LOG_TPC;
  constexpr int COSETS_PER_IT = BLK / TPC;
  constexpr unsigned BS = OMEGA_LOG_ORDER - LOG_N;
  static_assert(BLK % TPC == 0, "BLK must be a multiple of TPC");
  // Cross-thread stages use __shfl_xor_sync, which is warp-scoped: TPC must
  // fit in a single warp so the last cross stage's partner exchange stays
  // within 32 lanes.
  static_assert(TPC <= 32, "TPC > 32 would require cross-warp __shfl_xor_sync");

  using bfvec = typename bf_vec<VPT>::type;

  // Smem twiddle layout: stage-major, thread-position bank-cell within each stage.
  //   within-thread stage s in [0, LOG_VPT): (VPT >> (s+1)) cells per thread,
  //     offset (in TPC units) = VPT - (VPT >> s).
  //     The last within-thread stage (s = LOG_VPT-1) is the overall last stage
  //     iff LOG_N == LOG_VPT — in that case its twiddle multiplication is
  //     skipped and its smem slot is not allocated.
  //   cross-thread non-last stages (cs in [0, CROSS_NON_LAST)): 1 cell per
  //     thread per stage, after the within-thread block.
  constexpr int CROSS_TOTAL = LOG_N - LOG_VPT;                              // includes the final stage
  constexpr int CROSS_NON_LAST = (CROSS_TOTAL > 0) ? (CROSS_TOTAL - 1) : 0; // smem-backed cross stages
  constexpr bool LAST_WITHIN_HAS_TW = (LOG_N > LOG_VPT);                    // last within-thread stage has a twiddle slot
  constexpr int WITHIN_LAST_OFF_TPC = VPT - (VPT >> (LOG_VPT - 1));         // offset of stage LOG_VPT-1
  constexpr int CROSS_OFF_TPC = WITHIN_LAST_OFF_TPC + (LAST_WITHIN_HAS_TW ? 1 : 0);
  constexpr int TW_CELLS = (CROSS_OFF_TPC + CROSS_NON_LAST) * TPC;
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
#pragma unroll
    for (int s = 0; s < LOG_VPT; ++s) {
      const int stage_off = VPT - (VPT >> s);
      const int n_twiddles = VPT >> (s + 1);
      const bool stage_is_overall_last = (s == LOG_N - 1);
      if (!stage_is_overall_last) {
#pragma unroll
        for (int k = 0; k < (VPT >> 1); ++k) {
          if (k < n_twiddles) {
            smem_tw[(stage_off + k) * TPC + tp] =
                get_forward_twiddle_power(bitrev(tp * static_cast<unsigned>(n_twiddles) + static_cast<unsigned>(k), LOG_N - 1) << BS);
          }
        }
      }
    }
    if constexpr (CROSS_NON_LAST > 0) {
#pragma unroll
      for (int cs = 0; cs < CROSS_NON_LAST; ++cs) {
        const int s = LOG_VPT + cs;
        const unsigned mask_lanes = 1u << cs;
        const unsigned left_tp = tp & ~mask_lanes;
        const unsigned group = (left_tp * static_cast<unsigned>(VPT)) >> (s + 1);
        smem_tw[(CROSS_OFF_TPC + cs) * TPC + tp] = get_forward_twiddle_power(bitrev(group, LOG_N - 1) << BS);
      }
    }
  }

  // bitrev_N(row) where row = (tp << LOG_VPT) | r. bitrev(row, LOG_N) =
  //   (bitrev(r, LOG_VPT) << LOG_TPC) | bitrev(tp, LOG_TPC).
  // The per-r bitrev is computed via the device `bitrev(...)` helper —
  // ptxas folds __brev() on the loop-constant `r` after #pragma unroll.
  const unsigned tp_brev = (LOG_TPC > 0) ? bitrev(thread_pos, LOG_TPC) : 0u;
  unsigned bitrev_row[VPT];
#pragma unroll
  for (int r = 0; r < VPT; ++r)
    bitrev_row[r] = (bitrev(static_cast<unsigned>(r), LOG_VPT) << LOG_TPC) | tp_brev;

  // Setup: load this thread's VPT monomials, fold in the initial coset shift,
  // and precompute the per-row delta twiddle D[r] = omega^(Delta * bitrev(r))
  // where Delta = COSETS_PER_IT << K_shift is the absolute step in coset-
  // factor space.
  const unsigned c_rel = block_base + coset_in_it;
  const unsigned c_abs = static_cast<unsigned>(coset_index_base) + c_rel;
  const unsigned cfp0 = c_abs << K_shift;

  bf m_prime[VPT];
#pragma unroll
  for (int r = 0; r < VPT; ++r) {
    const unsigned row = (thread_pos << LOG_VPT) | static_cast<unsigned>(r);
    bf m = load_ca(monomials + row);
    if (bitrev_row[r] != 0u) {
      m = bf::mul(m, get_forward_twiddle_power(bitrev_row[r] * cfp0));
    }
    m_prime[r] = m;
  }

  const unsigned delta_cfp = static_cast<unsigned>(COSETS_PER_IT) << K_shift;
  bf D[VPT];
#pragma unroll
  for (int r = 0; r < VPT; ++r) {
    D[r] = (bitrev_row[r] == 0u) ? bf::ONE() : get_forward_twiddle_power(bitrev_row[r] * delta_cfp);
  }

  // shfl_xor mask: cross-thread partners are within a TPC-lane subwarp.
  const unsigned lane = tid & 31u;
  constexpr unsigned LANE_GROUP_MASK = (TPC >= 32) ? 0xFFFFFFFFu : ((1u << TPC) - 1u);
  const unsigned subwarp_mask = (TPC >= 32) ? 0xFFFFFFFFu : (LANE_GROUP_MASK << ((lane >> LOG_TPC) * TPC));

  for (unsigned it = 0; it < iters; ++it) {
    bf w[VPT];
#pragma unroll
    for (int r = 0; r < VPT; ++r)
      w[r] = m_prime[r];

    // Within-thread stages s in [0, LOG_VPT). Each stage halves the count of
    // within-block butterflies' twiddles (stage 0 has VPT/2 twiddles, stage 1
    // has VPT/4, ...). For LOG_N == LOG_VPT the last within-thread stage is
    // overall last and skips its twiddle multiplication.
#pragma unroll
    for (int s = 0; s < LOG_VPT; ++s) {
      const int dist = 1 << s;
      const int n_twiddles = VPT >> (s + 1);
      const int stage_off = VPT - (VPT >> s);
      const bool stage_is_overall_last = (s == LOG_N - 1);
      bf t[VPT >> 1];
      if (!stage_is_overall_last) {
#pragma unroll
        for (int k = 0; k < (VPT >> 1); ++k) {
          if (k < n_twiddles) {
            t[k] = smem_tw[(stage_off + k) * TPC + thread_pos];
          }
        }
      }
#pragma unroll
      for (int k = 0; k < (VPT >> 1); ++k) {
        const int block_idx = k >> s;
        const int intra = k & (dist - 1);
        const int lo = (block_idx << (s + 1)) | intra;
        const int hi = lo + dist;
        const bf sm = bf::add(w[lo], w[hi]);
        const bf df = bf::sub(w[lo], w[hi]);
        w[lo] = sm;
        if (stage_is_overall_last) {
          w[hi] = df;
        } else {
          w[hi] = bf::mul(df, t[block_idx]);
        }
      }
    }

    // Cross-thread stages s in [LOG_VPT, LOG_N) via shfl_xor. The final stage
    // skips the twiddle multiplication.
    if constexpr (CROSS_TOTAL > 0) {
#pragma unroll
      for (int cs = 0; cs < CROSS_TOTAL; ++cs) {
        const int s = LOG_VPT + cs;
        const unsigned mask_lanes = 1u << cs;
        const bool stage_is_overall_last = (s == LOG_N - 1);
        const bool is_lo = (thread_pos & mask_lanes) == 0u;
        bf t;
        if (!stage_is_overall_last) {
          t = smem_tw[(CROSS_OFF_TPC + cs) * TPC + thread_pos];
        }
#pragma unroll
        for (int r = 0; r < VPT; ++r) {
          const unsigned qu = __shfl_xor_sync(subwarp_mask, bf::into_raw_u32(w[r]), mask_lanes);
          const bf pv = bf::from_reduced_raw_repr(qu);
          const bf l = is_lo ? w[r] : pv;
          const bf rh = is_lo ? pv : w[r];
          if (stage_is_overall_last) {
            w[r] = is_lo ? bf::add(l, rh) : bf::sub(l, rh);
          } else {
            w[r] = is_lo ? bf::add(l, rh) : bf::mul(bf::sub(l, rh), t);
          }
        }
      }
    }

    // Vector store: 32 B aligned bf8 -> STG.E.ENL2.256 on sm_100+ (else two
    // STG.E.128 in PTX); 16 B aligned bf4 -> STG.E.128.
    const unsigned coset_rel = block_base + it * static_cast<unsigned>(COSETS_PER_IT) + coset_in_it;
    bf *coset_ptr = out + static_cast<size_t>(coset_rel) * coset_stride_bf + (thread_pos << LOG_VPT);
    bfvec packed;
#pragma unroll
    for (int r = 0; r < VPT; ++r)
      packed.values[r] = w[r];
    store_cs(reinterpret_cast<bfvec *>(coset_ptr), packed);

    // Running shift update m'[r] *= D[r] — advances to the next iter's coset.
#pragma unroll
    for (int r = 0; r < VPT; ++r) {
      m_prime[r] = bf::mul(m_prime[r], D[r]);
    }
  }
}

#define DEFINE_STREAMING_KERNEL_V8(LOG_N, BLK)                                                                                                                 \
  EXTERN NTT_STREAMING_LAUNCH_BOUNDS_V8(BLK)                                                                                                                   \
  __global__ void ab_monomials_to_evals_streaming_v8_##LOG_N##_stages_kernel(const bf *__restrict__ monomials, bf *__restrict__ out,                           \
                                                                             const int coset_index_base, const int coset_factor_shift,                         \
                                                                             const unsigned num_cosets, const unsigned long long coset_stride_bf) {            \
    monomials_to_evals_streaming_impl<LOG_N, 3, BLK>(monomials, out, coset_index_base, coset_factor_shift, num_cosets, static_cast<size_t>(coset_stride_bf));  \
  }

#define DEFINE_STREAMING_KERNEL_V4(LOG_N, BLK)                                                                                                                 \
  EXTERN NTT_STREAMING_LAUNCH_BOUNDS_V4(BLK)                                                                                                                   \
  __global__ void ab_monomials_to_evals_streaming_v4_##LOG_N##_stages_kernel(const bf *__restrict__ monomials, bf *__restrict__ out,                           \
                                                                             const int coset_index_base, const int coset_factor_shift,                         \
                                                                             const unsigned num_cosets, const unsigned long long coset_stride_bf) {            \
    monomials_to_evals_streaming_impl<LOG_N, 2, BLK>(monomials, out, coset_index_base, coset_factor_shift, num_cosets, static_cast<size_t>(coset_stride_bf));  \
  }

DEFINE_STREAMING_KERNEL_V8(3, 256)
DEFINE_STREAMING_KERNEL_V8(4, 256)
DEFINE_STREAMING_KERNEL_V8(5, 256)
DEFINE_STREAMING_KERNEL_V8(6, 256)
DEFINE_STREAMING_KERNEL_V8(7, 256)
DEFINE_STREAMING_KERNEL_V8(8, 256)

DEFINE_STREAMING_KERNEL_V4(2, 256)
DEFINE_STREAMING_KERNEL_V4(3, 256)
DEFINE_STREAMING_KERNEL_V4(4, 256)
DEFINE_STREAMING_KERNEL_V4(5, 256)
DEFINE_STREAMING_KERNEL_V4(6, 256)
DEFINE_STREAMING_KERNEL_V4(7, 256)

#undef DEFINE_STREAMING_KERNEL_V8
#undef DEFINE_STREAMING_KERNEL_V4
#undef NTT_STREAMING_LAUNCH_BOUNDS_V8
#undef NTT_STREAMING_LAUNCH_BOUNDS_V4

} // namespace airbender::ntt
