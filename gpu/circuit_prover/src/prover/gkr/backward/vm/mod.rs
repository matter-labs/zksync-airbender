pub(crate) mod compile;
pub(crate) mod desc;
#[cfg(all(test, feature = "bench"))]
mod gpu_tests;
pub(crate) mod lower;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cuda_struct_and_stub;

use self::desc::{BwdVmDesc, BWD_VM_CONST_DERIVED_E4_CAP};
use crate::primitives::field::E4;
use crate::prover::gkr::backward::flat::FLAT_CONST_MAX;
use crate::prover::ProverContext;

pub(crate) const BWD_VM_THREADS_PER_BLOCK: u32 = 128;
pub(crate) const BWD_VM_MIN_BUDGET_CELLS: u32 = 2;
pub(crate) const BWD_VM_MAX_BUDGET_CELLS: u32 = 16;
pub(crate) const BWD_VM_ERR_SOURCE_OOB: u32 = 128;

cuda_struct_and_stub! {
    static ab_gkr_flat_coefficients: [E4; FLAT_CONST_MAX];
}
cuda_struct_and_stub! {
    static ab_gkr_fwd_vm_const_derived_e4: [E4; BWD_VM_CONST_DERIVED_E4_CAP];
}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdVmRelease,
    desc: BwdVmDesc,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bwd_vm_release_kernel(desc: BwdVmDesc)
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrBwdVmValidate,
    desc: BwdVmDesc,
    error_flag: *mut u32,
    diagnostic_t0_t2: *mut E4,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_bwd_vm_validate_kernel(
        desc: BwdVmDesc,
        error_flag: *mut u32,
        diagnostic_t0_t2: *mut E4
    )
);

fn launch_config<'a>(
    desc: &BwdVmDesc,
    budget_cells: u32,
    context: &'a ProverContext,
) -> CudaLaunchConfig<'a> {
    assert!(
        (BWD_VM_MIN_BUDGET_CELLS..=BWD_VM_MAX_BUDGET_CELLS).contains(&budget_cells),
        "backward VM budget c{budget_cells} is outside c{BWD_VM_MIN_BUDGET_CELLS}..c{BWD_VM_MAX_BUDGET_CELLS}"
    );
    let logical_rows_per_block = BWD_VM_THREADS_PER_BLOCK / 2;
    CudaLaunchConfig::builder()
        .grid_dim(desc.logical_rows.max(1).div_ceil(logical_rows_per_block))
        .block_dim(BWD_VM_THREADS_PER_BLOCK)
        .dynamic_smem_bytes(
            budget_cells as usize * core::mem::size_of::<E4>() * BWD_VM_THREADS_PER_BLOCK as usize,
        )
        .stream(context.get_exec_stream())
        .build()
}

#[allow(dead_code)]
pub(crate) fn launch_bwd_vm_release(
    desc: &BwdVmDesc,
    budget_cells: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = launch_config(desc, budget_cells, context);
    let args = GkrBwdVmReleaseArguments::new(*desc);
    GkrBwdVmReleaseFunction(ab_gkr_bwd_vm_release_kernel).launch(&config, &args)
}

#[allow(dead_code)]
pub(crate) fn launch_bwd_vm_validate(
    desc: &BwdVmDesc,
    budget_cells: u32,
    error_flag: *mut u32,
    diagnostic_t0_t2: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = launch_config(desc, budget_cells, context);
    let args = GkrBwdVmValidateArguments::new(*desc, error_flag, diagnostic_t0_t2);
    GkrBwdVmValidateFunction(ab_gkr_bwd_vm_validate_kernel).launch(&config, &args)
}
