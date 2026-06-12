//! Stage-3 GKR eval-ISA bench harness
//! (spec: .agents/specs/2026-06-12-gkr-eval-isa-stage3-cuda-bench-design.md).
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))`. Both gates are
//! required: plain `cargo test -p circuit_prover` must not reference
//! `ab_gkr_bench_*` symbols (the bench `.cu` is only compiled into
//! `circuit_prover_native` under `-DAB_GKR_BENCH=ON`, so a plain `cfg(test)`
//! extern would fail to link), and a feature-gated non-test module could not
//! see dev-dependencies.

mod tests;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::field::BF;
use crate::prover::ProverContext;

pub(crate) const BENCH_INTERP_THREADS_PER_BLOCK: u32 = 128;

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBenchFwdInterpSmoke,
    src: *const BF,
    dst: *mut BF,
    count: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_interp_smoke_kernel(
        src: *const BF,
        dst: *mut BF,
        count: u32,
    )
);

pub(crate) fn launch_bench_fwd_interp_smoke(
    src: *const BF,
    dst: *mut BF,
    count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let grid_dim = count.max(1).div_ceil(BENCH_INTERP_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::basic(
        grid_dim,
        BENCH_INTERP_THREADS_PER_BLOCK,
        context.get_exec_stream(),
    );
    let args = GkrBenchFwdInterpSmokeArguments::new(src, dst, count);
    GkrBenchFwdInterpSmokeFunction(ab_gkr_bench_fwd_interp_smoke_kernel).launch(&config, &args)
}
