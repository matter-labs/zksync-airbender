mod resources;

#[cfg(test)]
pub(crate) use resources::{cpu_validate_dr_tail_shapes_pr, DrTailLayerPlanPr};
pub(crate) use resources::{dimension_reducing_slots_pr, DrTailPlanCursorPr};
pub use resources::{preflight_dr_tail_resources_pr, DrTailProofPlanPr};

use core::mem::{align_of, offset_of, size_of};
use std::collections::BTreeMap;

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_gkr_compiler::KERNEL_ARGUMENT_CEILING_BYTES;
use gpu_prover_context::ProverContext;

use super::capacity::DrTailCapacityDecisionPr;
use super::scheduled_execution::{note_device, ResourceEventPr};
use crate::backward::{
    GpuGKRDimensionReducingLayerSlots, GKR_DIM_REDUCING_INPUTS_PER_SLOT,
    GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, GKR_DIM_REDUCING_SLOTS,
};
use crate::upstream::{GKRAddress, PR};

pub(crate) const PR_DR_TAIL_MAX_SOURCES: usize = 10;
pub(crate) const PR_DR_TAIL_BLOCK_THREADS: u32 = 256;
pub(crate) const PR_DR_TAIL_MAX_REMAINING_ROUNDS: usize = 8;
pub(crate) const PR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE: usize = 128;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct DrTailSlotPr {
    pub(crate) input_source: [u16; GKR_DIM_REDUCING_INPUTS_PER_SLOT],
    pub(crate) batch_exp: [u16; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct DrTailMegakernelDescPr {
    pub(crate) enabled_mask: u32,
    pub(crate) folding_steps: u32,
    pub(crate) entry_round: u32,
    pub(crate) source_count: u32,
    pub(crate) source_ptrs: [*const PR; PR_DR_TAIL_MAX_SOURCES],
    pub(crate) final_sources: *mut PR,
    pub(crate) tau: *const PR,
    pub(crate) seed: *mut u8,
    pub(crate) claim: *mut PR,
    pub(crate) eq_prefactor: *mut PR,
    pub(crate) coeffs_out: *mut PR,
    pub(crate) challenges_out: *mut PR,
    pub(crate) batch_challenges: *const PR,
    pub(crate) slots: [DrTailSlotPr; GKR_DIM_REDUCING_SLOTS],
}

pub(crate) const PR_DR_TAIL_ARGUMENT_BYTES: usize =
    size_of::<DrTailMegakernelDescPr>() + size_of::<*mut PR>();

const _: () = {
    assert!(size_of::<DrTailSlotPr>() == 8);
    assert!(align_of::<DrTailSlotPr>() == 2);
    assert!(offset_of!(DrTailSlotPr, input_source) == 0);
    assert!(offset_of!(DrTailSlotPr, batch_exp) == 4);
    assert!(size_of::<DrTailMegakernelDescPr>() == 200);
    assert!(align_of::<DrTailMegakernelDescPr>() == 8);
    assert!(PR_DR_TAIL_ARGUMENT_BYTES == 208);
    assert!(PR_DR_TAIL_ARGUMENT_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(DrTailMegakernelDescPr, enabled_mask) == 0);
    assert!(offset_of!(DrTailMegakernelDescPr, folding_steps) == 4);
    assert!(offset_of!(DrTailMegakernelDescPr, entry_round) == 8);
    assert!(offset_of!(DrTailMegakernelDescPr, source_count) == 12);
    assert!(offset_of!(DrTailMegakernelDescPr, source_ptrs) == 16);
    assert!(offset_of!(DrTailMegakernelDescPr, final_sources) == 96);
    assert!(offset_of!(DrTailMegakernelDescPr, tau) == 104);
    assert!(offset_of!(DrTailMegakernelDescPr, seed) == 112);
    assert!(offset_of!(DrTailMegakernelDescPr, claim) == 120);
    assert!(offset_of!(DrTailMegakernelDescPr, eq_prefactor) == 128);
    assert!(offset_of!(DrTailMegakernelDescPr, coeffs_out) == 136);
    assert!(offset_of!(DrTailMegakernelDescPr, challenges_out) == 144);
    assert!(offset_of!(DrTailMegakernelDescPr, batch_challenges) == 152);
    assert!(offset_of!(DrTailMegakernelDescPr, slots) == 160);
};

cuda_kernel!(
    pub(crate) PrDrTailMegakernel,
    ab_pr_gkr_dr_tail_megakernel(desc: DrTailMegakernelDescPr, global_state: *mut PR,)
);

fn assert_capacity_matches_descriptor(
    desc: &DrTailMegakernelDescPr,
    capacity: &DrTailCapacityDecisionPr,
) {
    let folding_steps = desc.folding_steps as usize;
    let entry_round = desc.entry_round as usize;
    let source_count = desc.source_count as usize;
    assert_eq!(
        entry_round, capacity.entry_round,
        "Proth120 DR-tail entry round differs from the admitted capacity"
    );
    let remaining_rounds = folding_steps
        .checked_sub(entry_round)
        .expect("Proth120 DR-tail entry round exceeds the folding steps");
    assert!(
        (1..=PR_DR_TAIL_MAX_REMAINING_ROUNDS).contains(&remaining_rounds),
        "Proth120 DR-tail remaining rounds out of range"
    );
    assert!(
        (1usize << (remaining_rounds - 1)) <= PR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE,
        "Proth120 DR-tail first-round accumulator exceeds the block"
    );
    assert!(
        (1..=PR_DR_TAIL_MAX_SOURCES).contains(&source_count),
        "Proth120 DR-tail source count out of range"
    );
    for source in desc.source_ptrs.iter().take(source_count) {
        assert_eq!(
            *source as usize % 32,
            0,
            "Proth120 DR-tail packed entry load requires 32-byte aligned canonical source pointers"
        );
    }
    for (name, pointer) in [
        ("final sources", desc.final_sources as usize),
        ("tau", desc.tau as usize),
        ("seed", desc.seed as usize),
        ("claim", desc.claim as usize),
        ("eq prefactor", desc.eq_prefactor as usize),
        ("coefficients", desc.coeffs_out as usize),
        ("challenges", desc.challenges_out as usize),
        ("batch challenges", desc.batch_challenges as usize),
    ] {
        assert_ne!(pointer, 0, "Proth120 DR-tail {name} pointer is null");
    }
    assert!((1usize << remaining_rounds) <= PR_DR_TAIL_BLOCK_THREADS as usize);
}

pub(crate) fn launch_dr_tail_megakernel_pr(
    desc: DrTailMegakernelDescPr,
    capacity: &DrTailCapacityDecisionPr,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_capacity_matches_descriptor(&desc, capacity);
    let mut state = context.alloc_with_extra_alignment::<PR, 1>(
        capacity.global_state_bytes / size_of::<PR>(),
        AllocationPlacement::Top,
    )?;
    let state_ptr = state.as_mut_ptr();
    assert_eq!(
        state_ptr as usize % 32,
        0,
        "Proth120 DR-tail packed working state alignment"
    );
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(PR_DR_TAIL_BLOCK_THREADS)
        .dynamic_smem_bytes(capacity.dynamic_smem_bytes)
        .stream(context.get_exec_stream())
        .build();
    note_device(
        context,
        "backward.dr",
        None,
        ResourceEventPr::Allocated,
        "bwd.dr_tail.state",
        &state,
    );
    PrDrTailMegakernelFunction::default()
        .launch(&config, &PrDrTailMegakernelArguments::new(desc, state_ptr))?;
    note_device(
        context,
        "backward.dr",
        None,
        ResourceEventPr::Released,
        "bwd.dr_tail.state",
        &state,
    );
    drop(state);
    Ok(())
}

pub(crate) fn encode_dr_tail_slots_pr(
    layer_slots: &GpuGKRDimensionReducingLayerSlots,
    folding_addresses: &[GKRAddress],
    aliases: Option<&BTreeMap<GKRAddress, GKRAddress>>,
) -> [DrTailSlotPr; GKR_DIM_REDUCING_SLOTS] {
    let mut slots = [DrTailSlotPr::default(); GKR_DIM_REDUCING_SLOTS];
    for (slot_idx, slot) in layer_slots.iter_enabled() {
        let mut encoded = DrTailSlotPr::default();
        for (input_idx, address) in slot.inputs.iter().copied().enumerate() {
            let canonical = aliases
                .and_then(|aliases| aliases.get(&address))
                .copied()
                .unwrap_or(address);
            let source_idx = folding_addresses
                .binary_search(&canonical)
                .expect("Proth120 DR-tail source must be in the canonical publication");
            encoded.input_source[input_idx] = source_idx as u16;
        }
        encoded.batch_exp = slot.batch_exp;
        slots[slot_idx] = encoded;
    }
    slots
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailRawAttributesPr {
    pub(crate) static_smem_bytes: usize,
    pub(crate) local_bytes: usize,
    pub(crate) max_dynamic_smem_bytes: usize,
}

pub(crate) fn dr_tail_attributes_pr() -> CudaResult<DrTailRawAttributesPr> {
    let function = PrDrTailMegakernelFunction::default();
    let mut raw = std::mem::MaybeUninit::<era_cudart_sys::CudaFuncAttributes>::zeroed();
    let status =
        unsafe { era_cudart_sys::cudaFuncGetAttributes(raw.as_mut_ptr(), function.as_ptr()) };
    if status != era_cudart_sys::CudaError::Success {
        return Err(status);
    }
    let raw = unsafe { raw.assume_init() };
    Ok(DrTailRawAttributesPr {
        static_smem_bytes: raw.sharedSizeBytes,
        local_bytes: raw.localSizeBytes,
        max_dynamic_smem_bytes: raw.maxDynamicSharedSizeBytes.max(0) as usize,
    })
}

pub(crate) fn dr_tail_device_optin_cap_bytes_pr(device_id: i32) -> CudaResult<usize> {
    let cap = era_cudart::device::device_get_attribute(
        era_cudart_sys::CudaDeviceAttr::MaxSharedMemoryPerBlockOptin,
        device_id,
    )?;
    Ok(cap.max(0) as usize)
}

pub(crate) fn set_dr_tail_max_dynamic_smem_bytes_pr(bytes: usize) -> CudaResult<()> {
    let function = PrDrTailMegakernelFunction::default();
    let status = unsafe {
        cudaFuncSetAttribute(
            function.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            i32::try_from(bytes).expect("Proth120 DR-tail dynamic shared memory exceeds i32"),
        )
    };
    if status != era_cudart_sys::CudaError::Success {
        return Err(status);
    }
    Ok(())
}

pub(crate) fn dr_tail_occupancy_pr(dynamic_smem_bytes: usize) -> CudaResult<u32> {
    let function = PrDrTailMegakernelFunction::default();
    max_active_blocks_per_multiprocessor(
        &function,
        PR_DR_TAIL_BLOCK_THREADS as i32,
        dynamic_smem_bytes,
    )
    .map(|blocks| blocks.max(0) as u32)
}
