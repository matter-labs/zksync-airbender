pub(crate) mod compile;
pub(crate) mod desc;
#[cfg(all(test, feature = "bench"))]
mod gpu_tests;
pub(crate) mod lower;
#[cfg(all(test, feature = "bench"))]
mod report;

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

macro_rules! declare_bwd_vm_release_kernel {
    ($signature:ident, $symbol:ident) => {
        cuda_kernel_signature_arguments_and_function!(
            pub(crate) $signature,
            desc: BwdVmDesc,
        );
        cuda_kernel_declaration!(pub(crate) $symbol(desc: BwdVmDesc));
    };
}

macro_rules! declare_bwd_vm_validate_kernel {
    ($signature:ident, $symbol:ident) => {
        cuda_kernel_signature_arguments_and_function!(
            pub(crate) $signature,
            desc: BwdVmDesc,
            error_flag: *mut u32,
            diagnostic_t0_t2: *mut E4,
        );
        cuda_kernel_declaration!(pub(crate)
            $symbol(
                desc: BwdVmDesc,
                error_flag: *mut u32,
                diagnostic_t0_t2: *mut E4
            )
        );
    };
}

declare_bwd_vm_release_kernel!(GkrBwdVmReleaseD0, ab_gkr_bwd_vm_release_d0_kernel);
declare_bwd_vm_release_kernel!(GkrBwdVmReleaseD1, ab_gkr_bwd_vm_release_d1_kernel);
declare_bwd_vm_release_kernel!(GkrBwdVmReleaseD2, ab_gkr_bwd_vm_release_d2_kernel);
declare_bwd_vm_release_kernel!(GkrBwdVmReleaseD3, ab_gkr_bwd_vm_release_d3_kernel);
declare_bwd_vm_validate_kernel!(GkrBwdVmValidateD0, ab_gkr_bwd_vm_validate_d0_kernel);
declare_bwd_vm_validate_kernel!(GkrBwdVmValidateD1, ab_gkr_bwd_vm_validate_d1_kernel);
declare_bwd_vm_validate_kernel!(GkrBwdVmValidateD2, ab_gkr_bwd_vm_validate_d2_kernel);
declare_bwd_vm_validate_kernel!(GkrBwdVmValidateD3, ab_gkr_bwd_vm_validate_d3_kernel);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BwdVmKernelDepth {
    D0,
    D1,
    D2,
    D3,
}

fn bwd_vm_kernel_depth(round: u32) -> BwdVmKernelDepth {
    match round {
        0 => BwdVmKernelDepth::D0,
        1 => BwdVmKernelDepth::D1,
        2 => BwdVmKernelDepth::D2,
        3 => BwdVmKernelDepth::D3,
        _ => BwdVmKernelDepth::D1,
    }
}

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
    match bwd_vm_kernel_depth(desc.n_round_challenges) {
        BwdVmKernelDepth::D0 => GkrBwdVmReleaseD0Function(ab_gkr_bwd_vm_release_d0_kernel)
            .launch(&config, &GkrBwdVmReleaseD0Arguments::new(*desc)),
        BwdVmKernelDepth::D1 => GkrBwdVmReleaseD1Function(ab_gkr_bwd_vm_release_d1_kernel)
            .launch(&config, &GkrBwdVmReleaseD1Arguments::new(*desc)),
        BwdVmKernelDepth::D2 => GkrBwdVmReleaseD2Function(ab_gkr_bwd_vm_release_d2_kernel)
            .launch(&config, &GkrBwdVmReleaseD2Arguments::new(*desc)),
        BwdVmKernelDepth::D3 => GkrBwdVmReleaseD3Function(ab_gkr_bwd_vm_release_d3_kernel)
            .launch(&config, &GkrBwdVmReleaseD3Arguments::new(*desc)),
    }
}

#[allow(dead_code)]
pub(crate) fn bwd_vm_release_blocks_per_sm(round: u32, budget_cells: u32) -> CudaResult<i32> {
    assert!(
        (BWD_VM_MIN_BUDGET_CELLS..=BWD_VM_MAX_BUDGET_CELLS).contains(&budget_cells),
        "backward VM occupancy budget outside supported range"
    );
    let dynamic_smem_bytes =
        budget_cells as usize * core::mem::size_of::<E4>() * BWD_VM_THREADS_PER_BLOCK as usize;
    match bwd_vm_kernel_depth(round) {
        BwdVmKernelDepth::D0 => era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &GkrBwdVmReleaseD0Function(ab_gkr_bwd_vm_release_d0_kernel),
            BWD_VM_THREADS_PER_BLOCK as i32,
            dynamic_smem_bytes,
        ),
        BwdVmKernelDepth::D1 => era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &GkrBwdVmReleaseD1Function(ab_gkr_bwd_vm_release_d1_kernel),
            BWD_VM_THREADS_PER_BLOCK as i32,
            dynamic_smem_bytes,
        ),
        BwdVmKernelDepth::D2 => era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &GkrBwdVmReleaseD2Function(ab_gkr_bwd_vm_release_d2_kernel),
            BWD_VM_THREADS_PER_BLOCK as i32,
            dynamic_smem_bytes,
        ),
        BwdVmKernelDepth::D3 => era_cudart::occupancy::max_active_blocks_per_multiprocessor(
            &GkrBwdVmReleaseD3Function(ab_gkr_bwd_vm_release_d3_kernel),
            BWD_VM_THREADS_PER_BLOCK as i32,
            dynamic_smem_bytes,
        ),
    }
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
    match bwd_vm_kernel_depth(desc.n_round_challenges) {
        BwdVmKernelDepth::D0 => GkrBwdVmValidateD0Function(ab_gkr_bwd_vm_validate_d0_kernel)
            .launch(
                &config,
                &GkrBwdVmValidateD0Arguments::new(*desc, error_flag, diagnostic_t0_t2),
            ),
        BwdVmKernelDepth::D1 => GkrBwdVmValidateD1Function(ab_gkr_bwd_vm_validate_d1_kernel)
            .launch(
                &config,
                &GkrBwdVmValidateD1Arguments::new(*desc, error_flag, diagnostic_t0_t2),
            ),
        BwdVmKernelDepth::D2 => GkrBwdVmValidateD2Function(ab_gkr_bwd_vm_validate_d2_kernel)
            .launch(
                &config,
                &GkrBwdVmValidateD2Arguments::new(*desc, error_flag, diagnostic_t0_t2),
            ),
        BwdVmKernelDepth::D3 => GkrBwdVmValidateD3Function(ab_gkr_bwd_vm_validate_d3_kernel)
            .launch(
                &config,
                &GkrBwdVmValidateD3Arguments::new(*desc, error_flag, diagnostic_t0_t2),
            ),
    }
}

#[cfg(test)]
mod tests {
    use super::{BwdVmKernelDepth, bwd_vm_kernel_depth};

    #[test]
    fn backward_vm_kernel_depth_mapping_is_exact() {
        assert_eq!(bwd_vm_kernel_depth(0), BwdVmKernelDepth::D0);
        assert_eq!(bwd_vm_kernel_depth(1), BwdVmKernelDepth::D1);
        assert_eq!(bwd_vm_kernel_depth(2), BwdVmKernelDepth::D2);
        assert_eq!(bwd_vm_kernel_depth(3), BwdVmKernelDepth::D3);
        for round in 4..=24 {
            assert_eq!(bwd_vm_kernel_depth(round), BwdVmKernelDepth::D1);
        }
    }
}
