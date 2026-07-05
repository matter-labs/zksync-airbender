//! fwd-VM program acquisition (Task 1, host-only) for the planned CUDA
//! interpreter over `gkr_eval_isa` fwd-VM `CompiledCircuit` programs.
//!
//! Compiled ONLY under `cfg(all(test, feature = "bench"))` (inherited from
//! `bench_interp`, see `bench_interp/mod.rs`). No production wiring.

pub(crate) mod compile;
pub(crate) mod lower;
pub(crate) mod resolvers;
mod tests;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use self::lower::InterpDesc3;
use super::{InterpResidency, BENCH_INTERP_DEFAULT_SMEM_CAP, BENCH_INTERP_THREADS_PER_BLOCK};
use crate::prover::ProverContext;

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBenchFwdVm,
    desc: InterpDesc3,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_vm_ldg_kernel(desc: InterpDesc3)
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bench_fwd_vm_ldc_kernel(desc: InterpDesc3)
);

/// Per-block dynamic-smem the fwd-VM cell file needs: `budget` u32 lanes per
/// thread (Base cell = 1 lane, Ext = 4 lanes 4-aligned), interleaved
/// `smem[c * blockDim.x + t]` — matches the `.cu`'s
/// `extern __shared__ u32 fwd_vm_smem[]` sizing.
pub(crate) fn fwd_vm_dynamic_smem_bytes(budget: u32, threads_per_block: u32) -> usize {
    budget as usize * std::mem::size_of::<u32>() * threads_per_block as usize
}

/// Launch the fwd-VM interpreter kernel (row-per-thread) over `desc.count`
/// rows. For `InterpResidency::Ldc` the caller must already have uploaded
/// `setup.lanes` via `upload_bench_program_to_constant` (and may null
/// `desc.program_ldg`). Enqueues on `exec_stream`.
pub(crate) fn launch_fwd_vm(
    desc: &InterpDesc3,
    residency: InterpResidency,
    context: &ProverContext,
) -> CudaResult<()> {
    let tpb = BENCH_INTERP_THREADS_PER_BLOCK;
    let grid_dim = desc.count.max(1).div_ceil(tpb);
    let smem = fwd_vm_dynamic_smem_bytes(desc.budget, tpb);
    // Committed budgets are 16 cells (8 KB/block at 128 threads) — far below
    // the 48 KB default cap, so no large-smem opt-in path is needed here.
    assert!(
        smem <= BENCH_INTERP_DEFAULT_SMEM_CAP,
        "fwd-VM smem {smem} exceeds the default cap; add the opt-in before raising budgets"
    );
    let kernel = match residency {
        InterpResidency::Ldg => ab_gkr_bench_fwd_vm_ldg_kernel,
        InterpResidency::Ldc => ab_gkr_bench_fwd_vm_ldc_kernel,
    };
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(tpb)
        .dynamic_smem_bytes(smem)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrBenchFwdVmArguments::new(*desc);
    GkrBenchFwdVmFunction(kernel).launch(&config, &args)
}
