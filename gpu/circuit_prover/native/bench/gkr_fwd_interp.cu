#include "../prover/gkr/forward/flat.cuh"

namespace airbender::prover::gkr::bench {

// 128/4 mirrors the flat kernel's launch bound (flat_layer.cu) and must stay
// >= BENCH_INTERP_THREADS_PER_BLOCK on the Rust side.
// Stub: copies source 0 (bf) to output 0 per row. Replaced by the real
// interpreter in the next task; exists so the build/link/launch path is
// proven, including the include of flat.cuh from the bench dir.
EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_smoke_kernel(const bf *src, bf *dst, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  dst[gid] = src[gid];
}

} // namespace airbender::prover::gkr::bench
