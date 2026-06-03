// DIT engine production EXTERN wrappers: one unmangled, cuda_kernel!-bindable
// __global__ symbol per (LOG_N, LOG_VPT) config. EXTERN = extern "C" [[maybe_unused]].
// ntt_single/ntt_two_pass are __device__ (see dit_kernels.cuh); these thin
// __global__ wrappers carry the launch bounds. Bound + launched by the Rust
// launcher monomials_to_evals_dit (gpu/ntt/src/ntt/dit.rs).
#include "dit_kernels.cuh"
namespace airbender {
namespace ntt {

#define DIT_SINGLE_WRAPPER(LOGN, LOGVPT)                                                                                                                       \
  EXTERN __launch_bounds__(4u * 32u)                                                                                                                           \
      __global__ void ab_dit_single_##LOGN##_##LOGVPT(const bf *mono, const bf *tw_clean, bf *out, u32 cfp0, u32 step, u32 cstride) {                          \
    ntt_single<LOGN, LOGVPT, 4u, 8u, StoreMode::CS, 0u>(mono, tw_clean, out, cfp0, step, cstride);                                                             \
  }

#define DIT_TWO_PASS_WRAPPER(LOGN, LOGVPT)                                                                                                                     \
  EXTERN __launch_bounds__(NttTwoPassGeom<LOGN, LOGVPT>::THREADS, 1u) __global__ void ab_dit_two_pass_##LOGN##_##LOGVPT(                                       \
      const bf *mono, const bf *tw_p1, const bf *tw_p2, const bf *d_tab, bf *out, u32 cfp0, u32 step, u32 num_cosets, u32 cstride) {                           \
    ntt_two_pass<LOGN, LOGVPT, StoreMode::CS, 1u>(mono, tw_p1, tw_p2, d_tab, out, cfp0, step, num_cosets, cstride);                                            \
  }

// Streaming single-pass (guarded grid-stride + delta walk): the production
// single-pass launch path (unified with two-pass on the streaming/diagonal
// strategy). The static ntt_single wrappers above remain for the parity tests.
#define DIT_SINGLE_STREAM_WRAPPER(LOGN, LOGVPT)                                                                                                                \
  EXTERN __launch_bounds__(4u * 32u)                                                                                                                           \
      __global__ void ab_dit_single_stream_##LOGN##_##LOGVPT(const bf *mono, const bf *tw_clean, bf *out, u32 cfp0, u32 step, u32 num_cosets, u32 cstride) {   \
    ntt_single_stream<LOGN, LOGVPT, 4u, StoreMode::CS>(mono, tw_clean, out, cfp0, step, num_cosets, cstride);                                                  \
  }

// single-pass: v8 LOG_N 3..8, v4 LOG_N 2..7
DIT_SINGLE_WRAPPER(3, 3)
DIT_SINGLE_WRAPPER(4, 3)
DIT_SINGLE_WRAPPER(5, 3)
DIT_SINGLE_WRAPPER(6, 3)
DIT_SINGLE_WRAPPER(7, 3)
DIT_SINGLE_WRAPPER(8, 3)
DIT_SINGLE_WRAPPER(2, 2)
DIT_SINGLE_WRAPPER(3, 2)
DIT_SINGLE_WRAPPER(4, 2)
DIT_SINGLE_WRAPPER(5, 2)
DIT_SINGLE_WRAPPER(6, 2)
DIT_SINGLE_WRAPPER(7, 2)
// streaming single-pass: same config set (v8 3..8, v4 2..7)
DIT_SINGLE_STREAM_WRAPPER(3, 3)
DIT_SINGLE_STREAM_WRAPPER(4, 3)
DIT_SINGLE_STREAM_WRAPPER(5, 3)
DIT_SINGLE_STREAM_WRAPPER(6, 3)
DIT_SINGLE_STREAM_WRAPPER(7, 3)
DIT_SINGLE_STREAM_WRAPPER(8, 3)
DIT_SINGLE_STREAM_WRAPPER(2, 2)
DIT_SINGLE_STREAM_WRAPPER(3, 2)
DIT_SINGLE_STREAM_WRAPPER(4, 2)
DIT_SINGLE_STREAM_WRAPPER(5, 2)
DIT_SINGLE_STREAM_WRAPPER(6, 2)
DIT_SINGLE_STREAM_WRAPPER(7, 2)
// two-pass: v8 LOG_N 9..13, v4 LOG_N 8..12
DIT_TWO_PASS_WRAPPER(9, 3)
DIT_TWO_PASS_WRAPPER(10, 3)
DIT_TWO_PASS_WRAPPER(11, 3)
DIT_TWO_PASS_WRAPPER(12, 3)
DIT_TWO_PASS_WRAPPER(13, 3)
DIT_TWO_PASS_WRAPPER(8, 2)
DIT_TWO_PASS_WRAPPER(9, 2)
DIT_TWO_PASS_WRAPPER(10, 2)
DIT_TWO_PASS_WRAPPER(11, 2)
DIT_TWO_PASS_WRAPPER(12, 2)

#undef DIT_SINGLE_WRAPPER
#undef DIT_SINGLE_STREAM_WRAPPER
#undef DIT_TWO_PASS_WRAPPER

} // namespace ntt
} // namespace airbender
