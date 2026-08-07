//! Production forward VM.

pub(crate) mod desc;
pub(crate) mod lower;
mod output;
pub(crate) mod production_bind;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cuda_struct_and_stub;

use self::desc::{FwdVmDesc, CONST_DERIVED_E4_CAP};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

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
