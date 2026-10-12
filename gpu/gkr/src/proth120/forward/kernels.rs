use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_prover_context::ProverContext;

use super::desc::FwdVmDesc;
use crate::upstream::PR;

cuda_kernel_signature_arguments_and_function!(pub(crate) PrForwardVm, desc: FwdVmDesc);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_fwd_vm_kernel(desc: FwdVmDesc));
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_dim_reducing_forward_tower_kernel(batch: crate::forward::kernels::GpuGKRDimensionReducingForwardTowerBatch<PR>));
cuda_kernel_signature_arguments_and_function!(pub(crate) PrEqGroupTables, point: *const PR, offset: u32, count: u32, groups: *mut PR);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_build_eq_group_tables_kernel(point: *const PR, offset: u32, count: u32, groups: *mut PR));
cuda_kernel_signature_arguments_and_function!(pub(crate) PrEqHighLow, point: *const PR, offset: u32, count: u32, high0: *mut PR, high1: *mut PR, low: *mut PR);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_build_eq_high_low_from_point_kernel(point: *const PR, offset: u32, count: u32, high0: *mut PR, high1: *mut PR, low: *mut PR));
cuda_kernel_signature_arguments_and_function!(pub(crate) PrEqValues, groups: *const PR, count: u32, values: *mut PR, len: u32);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_build_eq_values_from_group_tables_kernel(groups: *const PR, count: u32, values: *mut PR, len: u32));
cuda_kernel_signature_arguments_and_function!(pub(crate) PrInitialInnerProduct, polys: *const PR, eq: *const PR, len: u32, claims: *mut PR);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_initial_inner_product_kernel(polys: *const PR, eq: *const PR, len: u32, claims: *mut PR));

#[cfg(test)]
pub(crate) fn vm_function() -> PrForwardVmFunction {
    PrForwardVmFunction(ab_pr_gkr_fwd_vm_kernel)
}

pub(crate) fn launch_vm(desc: &FwdVmDesc, context: &ProverContext) -> CudaResult<()> {
    assert!(desc.count > 0, "Proth120 forward VM has zero rows");
    let config = CudaLaunchConfig::basic(desc.count.div_ceil(128), 128, context.get_exec_stream());
    PrForwardVmFunction(ab_pr_gkr_fwd_vm_kernel).launch(&config, &PrForwardVmArguments::new(*desc))
}

pub(crate) fn launch_eq_values(
    point: *const PR,
    count: u32,
    groups: *mut PR,
    values: *mut PR,
    context: &ProverContext,
) -> CudaResult<()> {
    let group_count = crate::backward::eq_group_count(count as usize);
    let config = CudaLaunchConfig::basic(group_count as u32, 256, context.get_exec_stream());
    PrEqGroupTablesFunction(ab_pr_gkr_build_eq_group_tables_kernel).launch(
        &config,
        &PrEqGroupTablesArguments::new(point, 0, count, groups),
    )?;
    let len = 1u32
        .checked_shl(count)
        .expect("Proth120 eq value count overflow");
    let config = CudaLaunchConfig::basic(len.div_ceil(256), 256, context.get_exec_stream());
    PrEqValuesFunction(ab_pr_gkr_build_eq_values_from_group_tables_kernel).launch(
        &config,
        &PrEqValuesArguments::new(groups, count, values, len),
    )
}

pub(crate) fn launch_eq_high_low(
    point: *const PR,
    count: u32,
    high_0: *mut PR,
    high_1: *mut PR,
    low: *mut PR,
    context: &ProverContext,
) -> CudaResult<()> {
    let blocks = crate::backward::eq_group_count(count as usize).max(2);
    let config = CudaLaunchConfig::basic(blocks as u32, 256, context.get_exec_stream());
    PrEqHighLowFunction(ab_pr_gkr_build_eq_high_low_from_point_kernel).launch(
        &config,
        &PrEqHighLowArguments::new(point, 0, count, high_0, high_1, low),
    )
}

pub(crate) fn launch_initial_inner_products(
    polys: *const PR,
    count: usize,
    eq: *const PR,
    len: u32,
    claims: *mut PR,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(
        u32::try_from(count).expect("Proth120 initial claims exceed u32"),
        256,
        context.get_exec_stream(),
    );
    PrInitialInnerProductFunction(ab_pr_gkr_initial_inner_product_kernel).launch(
        &config,
        &PrInitialInnerProductArguments::new(polys, eq, len, claims),
    )
}
