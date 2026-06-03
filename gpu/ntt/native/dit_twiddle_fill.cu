// gpu/ntt/native/dit_twiddle_fill.cu
// One-time device fill of the DIT engine's per-config twiddle buffers, sourced
// from red's Rust-initialized ab_ntt_forward_powers (get_forward_twiddle_power).
// Mirrors the parity-proven Rust build_clean_triangle / build_coupled_triangle /
// build_coset_delta_table layouts (see gpu/ntt/src/ntt/tests/dit_engine.rs and
// git show d68a60a5^:gpu/ntt/native/dit_twiddles.cuh) index-for-index; there is
// NO host-side twiddle compute. The triangles are <= ~8K entries (one-time fill,
// not perf-critical).
//
// LAUNCH CONTRACT: every kernel here is correct ONLY for grid = 1 (single
// block). The clean/coupled kernels init their buffer to bf::ONE() then overwrite
// the active entries; the init/overwrite handoff is ordered by __syncthreads(),
// which synchronizes within ONE block only. Launchers MUST use grid = 1 (a large
// blockDim, e.g. 256, with the grid-stride loops below). Counts are <= ~8K so one
// block is sufficient.
//
// Config coverage (must match the hot kernels in dit_kernels_extern.cu):
//   single-pass: v8 (LOG_VPT=3) LOG_N 3..8; v4 (LOG_VPT=2) LOG_N 2..7.
//   two-pass:    v8 LOG_N 9..13; v4 LOG_N 8..12.
//
//   clean (LOG_M, LOG_VPT): every single-pass (LOG_N, LOG_VPT) used directly as
//     (LOG_M, LOG_VPT), PLUS every two-pass pass-2 (LOG_N2, LOG_VPT) where
//     LOG_N2 = min(LOG_N/2, LOG_VPT+3). The pass-2 set
//       {(4,2),(4,3),(5,2),(5,3),(6,3)}
//     is fully subsumed by the single-pass set, so the DEDUPED clean set is the
//     12 single-pass pairs:
//       (2,2) (3,2) (3,3) (4,2) (4,3) (5,2) (5,3) (6,2) (6,3) (7,2) (7,3) (8,3).
//   coupled (LOG_N, LOG_VPT): every two-pass config (10):
//       (8,2) (9,2) (9,3) (10,2) (10,3) (11,2) (11,3) (12,2) (12,3) (13,3).
//     LOG_N1 is derived inside the kernel: LOG_N1 = LOG_N - min(LOG_N/2, LOG_VPT+3).
//   d-table (LOG_N): every two-pass LOG_N: 8 9 10 11 12 13.
#include "context.cuh"      // get_forward_twiddle_power, bf, OMEGA_LOG_ORDER
#include "dit_geometry.cuh" // NttTwoPassGeom (for LOG_N1 / LOG_N2)
#include "dit_twiddles.cuh" // clean_triangle_count, coupled_triangle_count

namespace airbender {
namespace ntt {

// hbr(x, n): bit-reverse of x within n bits. Matches the Rust hbr() and the
// engine's bitrev(); __brev reverses 32 bits, the shift drops the high (32-n).
DEVICE_FORCEINLINE unsigned hbr_dev(unsigned x, unsigned n) { return __brev(x) >> (32u - n); }

// off(s) for the CLEAN triangle (LOG_TBL == LOG_M, THREADS == LANES).
template <unsigned LOG_M, unsigned LOG_VPT> DEVICE_FORCEINLINE unsigned clean_off(unsigned s) {
  constexpr unsigned VPT = 1u << LOG_VPT, LANES = 1u << (LOG_M - LOG_VPT);
  unsigned o = 0;
  for (unsigned k = 0; k < s; ++k)
    o += (k < LOG_VPT) ? (LANES * (VPT >> (k + 1u))) : (1u << (LOG_M - 1u - k));
  return o;
}

// off(s) for the COUPLED pass-1 triangle (LOG_TBL == LOG_N, THREADS == full block).
template <unsigned LOG_N, unsigned LOG_VPT> DEVICE_FORCEINLINE unsigned coupled_off(unsigned s) {
  constexpr unsigned VPT = 1u << LOG_VPT, THREADS = 1u << (LOG_N - LOG_VPT);
  unsigned o = 0;
  for (unsigned k = 0; k < s; ++k)
    o += (k < LOG_VPT) ? (THREADS * (VPT >> (k + 1u))) : (1u << (LOG_N - 1u - k));
  return o;
}

// Port of Rust build_clean_triangle<LOG_M, LOG_VPT>. Fills 2^M - 1 entries:
// init-to-ONE (matching vec![BF::ONE; count]), then overwrite active entries.
// Correct for grid = 1 ONLY (the init/overwrite handoff uses __syncthreads()).
template <unsigned LOG_M, unsigned LOG_VPT> DEVICE_FORCEINLINE void fill_clean_triangle(bf *dst) {
  constexpr unsigned VPT = 1u << LOG_VPT, LANES = 1u << (LOG_M - LOG_VPT);
  constexpr unsigned SHIFT = OMEGA_LOG_ORDER - LOG_M;
  constexpr unsigned COUNT = (LANES << LOG_VPT) - 1u; // 2^M - 1
  const unsigned tid = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;
  for (unsigned i = tid; i < COUNT; i += stride)
    dst[i] = bf::ONE(); // default; active entries overwritten below
  __syncthreads();
  // One thread per lane; each walks its LOG_M stages (cheap, COUNT small).
  for (unsigned lane = tid; lane < LANES; lane += stride) {
    for (unsigned s = 0; s < LOG_M; ++s) {
      if (s < LOG_VPT) {
        const unsigned U = VPT >> (s + 1u);
        for (unsigned q = 0; q < U; ++q) {
          const unsigned grp = lane * U + q;
          dst[clean_off<LOG_M, LOG_VPT>(s) + lane * U + q] = get_forward_twiddle_power(hbr_dev(grp, LOG_M - 1u) << SHIFT);
        }
      } else {
        const unsigned bg = lane >> (s + 1u - LOG_VPT);
        dst[clean_off<LOG_M, LOG_VPT>(s) + bg] = get_forward_twiddle_power(hbr_dev(bg, LOG_M - 1u) << SHIFT);
      }
    }
  }
}

// Port of Rust build_coupled_triangle<LOG_N, LOG_VPT, LOG_N1>. THREADS rows keyed
// on tid; the n2-block is folded into the global group index. Fills
// coupled_triangle_count entries (a multiple of 4). Correct for grid = 1 ONLY.
template <unsigned LOG_N, unsigned LOG_VPT> DEVICE_FORCEINLINE void fill_coupled_triangle(bf *dst) {
  constexpr unsigned LOG_N1 = NttTwoPassGeom<LOG_N, LOG_VPT>::LOG_N1;
  constexpr unsigned VPT = 1u << LOG_VPT, THREADS = 1u << (LOG_N - LOG_VPT);
  constexpr unsigned LANES_P1 = 1u << (LOG_N1 - LOG_VPT);
  constexpr unsigned SHIFT = OMEGA_LOG_ORDER - LOG_N;
  constexpr unsigned COUNT = coupled_triangle_count<LOG_N, LOG_VPT, LOG_N1>();
  const unsigned t = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;
  for (unsigned i = t; i < COUNT; i += stride)
    dst[i] = bf::ONE();
  __syncthreads();
  for (unsigned tid = t; tid < THREADS; tid += stride) {
    const unsigned n2 = tid >> (LOG_N1 - LOG_VPT);
    const unsigned lane = tid & (LANES_P1 - 1u);
    for (unsigned s = 0; s < LOG_N1; ++s) {
      if (s < LOG_VPT) {
        const unsigned U = VPT >> (s + 1u);
        for (unsigned q = 0; q < U; ++q) {
          const unsigned grp = (n2 << (LOG_N1 - 1u - s)) | (lane * U + q);
          dst[coupled_off<LOG_N, LOG_VPT>(s) + tid * U + q] = get_forward_twiddle_power(hbr_dev(grp, LOG_N - 1u) << SHIFT);
        }
      } else {
        const unsigned bg = lane >> (s + 1u - LOG_VPT);
        const unsigned grp = (n2 << (LOG_N1 - 1u - s)) | bg;
        dst[coupled_off<LOG_N, LOG_VPT>(s) + grp] = get_forward_twiddle_power(hbr_dev(grp, LOG_N - 1u) << SHIFT);
      }
    }
  }
}

// Port of Rust build_coset_delta_table<LOG_N>. Fills N entries in natural index
// order: d[i] = omega^(bitrev(i, LOG_N) * step_per_iter), i in [0, N). NO
// OMEGA_SHIFT (matches the kernel pow_omega convention). Every entry is written,
// so no init-to-ONE / __syncthreads() is needed; correct for any grid (single
// block used in practice for uniformity).
template <unsigned LOG_N> DEVICE_FORCEINLINE void fill_d_table(bf *dst, unsigned step_per_iter) {
  constexpr unsigned NN = 1u << LOG_N;
  const unsigned tid = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned stride = gridDim.x * blockDim.x;
  for (unsigned i = tid; i < NN; i += stride)
    dst[i] = get_forward_twiddle_power(hbr_dev(i, LOG_N) * step_per_iter); // u32 wrap matches Rust wrapping_mul
}

// --- EXTERN wrappers: one unmangled symbol per config (mirrors dit_kernels_extern.cu).
// No __launch_bounds__ (one-time, not perf-critical). Launch with grid = 1.
#define DIT_FILL_CLEAN(LOGM, LOGVPT)                                                                                                                           \
  EXTERN __global__ void ab_dit_fill_clean_triangle_##LOGM##_##LOGVPT(bf *dst) { fill_clean_triangle<LOGM, LOGVPT>(dst); }

#define DIT_FILL_COUPLED(LOGN, LOGVPT)                                                                                                                         \
  EXTERN __global__ void ab_dit_fill_coupled_triangle_##LOGN##_##LOGVPT(bf *dst) { fill_coupled_triangle<LOGN, LOGVPT>(dst); }

#define DIT_FILL_DTABLE(LOGN)                                                                                                                                  \
  EXTERN __global__ void ab_dit_fill_d_table_##LOGN(bf *dst, u32 step_per_iter) { fill_d_table<LOGN>(dst, step_per_iter); }

// clean: deduped 12-pair set (single-pass set; pass-2 LOG_N2 set is subsumed).
DIT_FILL_CLEAN(2, 2)
DIT_FILL_CLEAN(3, 2)
DIT_FILL_CLEAN(3, 3)
DIT_FILL_CLEAN(4, 2)
DIT_FILL_CLEAN(4, 3)
DIT_FILL_CLEAN(5, 2)
DIT_FILL_CLEAN(5, 3)
DIT_FILL_CLEAN(6, 2)
DIT_FILL_CLEAN(6, 3)
DIT_FILL_CLEAN(7, 2)
DIT_FILL_CLEAN(7, 3)
DIT_FILL_CLEAN(8, 3)

// coupled: every two-pass config (v8 LOG_N 9..13, v4 LOG_N 8..12).
DIT_FILL_COUPLED(9, 3)
DIT_FILL_COUPLED(10, 3)
DIT_FILL_COUPLED(11, 3)
DIT_FILL_COUPLED(12, 3)
DIT_FILL_COUPLED(13, 3)
DIT_FILL_COUPLED(8, 2)
DIT_FILL_COUPLED(9, 2)
DIT_FILL_COUPLED(10, 2)
DIT_FILL_COUPLED(11, 2)
DIT_FILL_COUPLED(12, 2)

// d-table: every two-pass LOG_N (8..13).
DIT_FILL_DTABLE(8)
DIT_FILL_DTABLE(9)
DIT_FILL_DTABLE(10)
DIT_FILL_DTABLE(11)
DIT_FILL_DTABLE(12)
DIT_FILL_DTABLE(13)

#undef DIT_FILL_CLEAN
#undef DIT_FILL_COUPLED
#undef DIT_FILL_DTABLE

} // namespace ntt
} // namespace airbender
