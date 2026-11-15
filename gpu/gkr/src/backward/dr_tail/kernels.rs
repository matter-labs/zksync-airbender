use core::mem::size_of;

use era_cudart::{
    execution::{CudaLaunchConfig, KernelArguments, KernelFunction},
    occupancy::max_active_blocks_per_multiprocessor,
    result::CudaResult,
};
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContext;

use crate::backward::dr_tail::resources::DrTailRawAttributes;

pub(crate) const DR_TAIL_MAX_SOURCES: usize = 10;
pub(crate) const DR_TAIL_SLOTS: usize = 5;
pub(crate) const DR_TAIL_BLOCK_THREADS: u32 = 256;
pub(crate) const DR_TAIL_MAX_REMAINING_ROUNDS: usize = 8;
pub(crate) const DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE: usize = 128;
pub(crate) const CUDA_KERNEL_ARGUMENT_CEILING_BYTES: usize = 32_764;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct DrTailSlot {
    pub(crate) input_source: [u16; 2],
    pub(crate) batch_exp: [u16; 2],
}

pub(crate) fn dr_tail_device_optin_cap_bytes(device_id: i32) -> CudaResult<usize> {
    let cap = era_cudart::device::device_get_attribute(
        era_cudart_sys::CudaDeviceAttr::MaxSharedMemoryPerBlockOptin,
        device_id,
    )?;
    Ok(cap.max(0) as usize)
}

pub(crate) fn launch_dr_tail_state<F, K, A>(
    global_state_bytes: usize,
    dynamic_smem_bytes: usize,
    threads: u32,
    function: &K,
    arguments: impl FnOnce(*mut F) -> A,
    context: &ProverContext,
) -> CudaResult<()>
where
    K: KernelFunction,
    A: KernelArguments<Signature = K::Signature>,
{
    let mut state = context.alloc_with_extra_alignment::<F, 1>(
        global_state_bytes / size_of::<F>(),
        AllocationPlacement::Top,
    )?;
    let state_ptr = state.as_mut_ptr();
    assert_eq!(
        state_ptr as usize % 32,
        0,
        "DR-tail packed working state alignment"
    );
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(threads)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(context.get_exec_stream())
        .build();
    function.launch(&config, &arguments(state_ptr))?;
    drop(state);
    Ok(())
}

pub(crate) fn kernel_attributes(function: &impl KernelFunction) -> CudaResult<DrTailRawAttributes> {
    let mut raw = std::mem::MaybeUninit::<era_cudart_sys::CudaFuncAttributes>::zeroed();
    let status =
        unsafe { era_cudart_sys::cudaFuncGetAttributes(raw.as_mut_ptr(), function.as_ptr()) };
    if status != era_cudart_sys::CudaError::Success {
        return Err(status);
    }
    let raw = unsafe { raw.assume_init() };
    Ok(DrTailRawAttributes {
        static_smem_bytes: raw.sharedSizeBytes,
        local_bytes: raw.localSizeBytes,
        max_dynamic_smem_bytes: raw.maxDynamicSharedSizeBytes.max(0) as usize,
    })
}

pub(crate) fn set_kernel_max_dynamic_smem(
    function: &impl KernelFunction,
    bytes: usize,
) -> CudaResult<()> {
    let bytes = i32::try_from(bytes).expect("DR-tail dynamic shared memory exceeds i32");
    let status = unsafe {
        cudaFuncSetAttribute(
            function.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            bytes,
        )
    };
    if status != era_cudart_sys::CudaError::Success {
        return Err(status);
    }
    Ok(())
}

pub(crate) fn kernel_occupancy(
    function: &impl KernelFunction,
    threads: u32,
    dynamic_smem_bytes: usize,
) -> CudaResult<u32> {
    max_active_blocks_per_multiprocessor(function, threads as i32, dynamic_smem_bytes)
        .map(|blocks| blocks.max(0) as u32)
}
