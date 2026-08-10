//! Production forward VM.

pub(crate) mod desc;
mod execution;
pub(crate) mod group_lower;
pub(crate) mod lower;
mod output;
pub(crate) mod production_bind;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cuda_struct_and_stub;

use self::desc::{FwdVmDesc, FwdVmGroupDesc, CONST_DERIVED_E4_CAP};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

pub(crate) use execution::{plan_device_groups, ForwardVmExecutionWitness};
pub use execution::{ForwardVmExecutionConfig, ForwardVmExecutionMode, ForwardVmStorePolicy};

pub(crate) const FWD_VM_THREADS_PER_BLOCK: u32 = 128;

cuda_struct_and_stub! { static ab_gkr_fwd_vm_const_derived_e4: [E4; CONST_DERIVED_E4_CAP]; }

// --- kernel declarations + launch wrappers ------------------------------------

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrFwdVmRelease,
    desc: FwdVmDesc,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_kernel(desc: FwdVmDesc)
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrFwdVmGroupedRelease,
    desc: FwdVmGroupDesc,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_device_streaming_kernel(
        desc: FwdVmGroupDesc,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_device_writeback_kernel(
        desc: FwdVmGroupDesc,
    )
);

/// Launch the forward VM with its fixed E4-bucket budget.
pub(crate) fn launch_fwd_vm(setup: &FwdVmDesc, context: &ProverContext) -> CudaResult<()> {
    let grid_dim = setup.count.max(1).div_ceil(FWD_VM_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmReleaseArguments::new(*setup);
    GkrFwdVmReleaseFunction(ab_gkr_fwd_vm_kernel).launch(&config, &args)
}

pub(crate) fn launch_grouped_fwd_vm_streaming(
    desc: &FwdVmGroupDesc,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(desc.layer_count > 0, "forward VM group must be non-empty");
    let grid_dim = desc.count.max(1).div_ceil(FWD_VM_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmGroupedReleaseArguments::new(*desc);
    GkrFwdVmGroupedReleaseFunction(ab_gkr_fwd_vm_device_streaming_kernel).launch(&config, &args)
}

pub(crate) fn launch_grouped_fwd_vm_writeback(
    desc: &FwdVmGroupDesc,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(desc.layer_count > 0, "forward VM group must be non-empty");
    let grid_dim = desc.count.max(1).div_ceil(FWD_VM_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid_dim)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmGroupedReleaseArguments::new(*desc);
    GkrFwdVmGroupedReleaseFunction(ab_gkr_fwd_vm_device_writeback_kernel).launch(&config, &args)
}
