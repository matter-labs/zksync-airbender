use core::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

use super::capacity::DrTailCapacityDecision;
use super::resources::{DrTailDeviceQueries, DrTailRawAttributes, DR_TAIL_OCCUPANCY_THREADS};

pub(crate) const DR_TAIL_MAX_SOURCES: usize = 10;
pub(crate) const DR_TAIL_SLOTS: usize = 5;
pub(crate) const DR_TAIL_BLOCK_THREADS: u32 = 256;
pub(crate) const DR_TAIL_MAX_REMAINING_ROUNDS: usize = 8;
pub(crate) const DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE: usize = 128;
const CUDA_KERNEL_ARGUMENT_CEILING_BYTES: usize = 32_764;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct DrTailSlot {
    pub(crate) input_source: [u16; 2],
    pub(crate) batch_exp: [u16; 2],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct DrTailMegakernelDesc {
    pub(crate) enabled_mask: u32,
    pub(crate) folding_steps: u32,
    pub(crate) entry_round: u32,
    pub(crate) source_count: u32,
    pub(crate) source_ptrs: [*const E4; DR_TAIL_MAX_SOURCES],
    pub(crate) final_sources: *mut E4,
    pub(crate) tau: *const E4,
    pub(crate) seed: *mut u32,
    pub(crate) claim: *mut E4,
    pub(crate) eq_prefactor: *mut E4,
    pub(crate) coeffs_out: *mut E4,
    pub(crate) challenges_out: *mut E4,
    pub(crate) slots: [DrTailSlot; DR_TAIL_SLOTS],
}

const _: () = {
    assert!(size_of::<DrTailSlot>() == 8);
    assert!(align_of::<DrTailSlot>() == 2);
    assert!(offset_of!(DrTailSlot, input_source) == 0);
    assert!(offset_of!(DrTailSlot, batch_exp) == 4);

    assert!(size_of::<DrTailMegakernelDesc>() == 192);
    assert!(align_of::<DrTailMegakernelDesc>() == 8);
    assert!(size_of::<DrTailMegakernelDesc>() <= CUDA_KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(DrTailMegakernelDesc, enabled_mask) == 0);
    assert!(offset_of!(DrTailMegakernelDesc, folding_steps) == 4);
    assert!(offset_of!(DrTailMegakernelDesc, entry_round) == 8);
    assert!(offset_of!(DrTailMegakernelDesc, source_count) == 12);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) == 16);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + size_of::<*const E4>() == 24);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 2 * size_of::<*const E4>() == 32);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 3 * size_of::<*const E4>() == 40);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 4 * size_of::<*const E4>() == 48);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 5 * size_of::<*const E4>() == 56);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 6 * size_of::<*const E4>() == 64);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 7 * size_of::<*const E4>() == 72);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 8 * size_of::<*const E4>() == 80);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 9 * size_of::<*const E4>() == 88);
    assert!(offset_of!(DrTailMegakernelDesc, final_sources) == 96);
    assert!(offset_of!(DrTailMegakernelDesc, tau) == 104);
    assert!(offset_of!(DrTailMegakernelDesc, seed) == 112);
    assert!(offset_of!(DrTailMegakernelDesc, claim) == 120);
    assert!(offset_of!(DrTailMegakernelDesc, eq_prefactor) == 128);
    assert!(offset_of!(DrTailMegakernelDesc, coeffs_out) == 136);
    assert!(offset_of!(DrTailMegakernelDesc, challenges_out) == 144);
    assert!(offset_of!(DrTailMegakernelDesc, slots) == 152);
};

cuda_kernel!(
    pub(crate) DrTailMegakernelE4,
    ab_gkr_dr_tail_megakernel_e4_kernel(desc: DrTailMegakernelDesc,)
);

fn assert_capacity_matches_descriptor(
    desc: &DrTailMegakernelDesc,
    capacity: &DrTailCapacityDecision,
) {
    let folding_steps = desc.folding_steps as usize;
    let entry_round = desc.entry_round as usize;
    let source_count = desc.source_count as usize;
    assert_eq!(entry_round, capacity.entry_round);
    assert_eq!(folding_steps, entry_round + capacity.remaining_rounds);
    assert!((1..=DR_TAIL_MAX_REMAINING_ROUNDS).contains(&capacity.remaining_rounds));
    let first_round_acc_size = 1usize << (capacity.remaining_rounds - 1);
    assert!(first_round_acc_size <= DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE);
    assert!((1..=DR_TAIL_MAX_SOURCES).contains(&source_count));
    for source in desc.source_ptrs.iter().take(source_count) {
        assert_eq!(
            *source as usize % 32,
            0,
            "DR-tail packed entry load requires 32-byte aligned canonical source pointers",
        );
    }
    assert_eq!(capacity.eq_suffix_offset, entry_round + 1);
    assert_eq!(capacity.eq_suffix_bits, folding_steps - entry_round - 1);
    assert_eq!(
        capacity.entry_cells_per_source,
        1usize << (capacity.remaining_rounds + 1)
    );
    assert!(capacity.entry_cells_per_source / 2 <= DR_TAIL_BLOCK_THREADS as usize);
    assert_eq!(
        capacity.state_bytes,
        source_count * capacity.entry_cells_per_source * size_of::<E4>()
    );
    assert_eq!(
        capacity.factored_eq_bytes,
        capacity.eq_group_count * super::super::kernels::GKR_EQ_GROUP_TABLE_LEN * size_of::<E4>()
    );
    assert_eq!(
        capacity.dynamic_smem_bytes,
        capacity.state_bytes + capacity.factored_eq_bytes
    );
}

/// Caller contract: admission has ensured that the kernel-wide dynamic shared
/// memory ceiling covers this launch.
pub(crate) fn launch_dr_tail_megakernel_e4(
    desc: DrTailMegakernelDesc,
    capacity: &DrTailCapacityDecision,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_capacity_matches_descriptor(&desc, capacity);
    let dynamic_smem_bytes = capacity.dynamic_smem_bytes;

    let function = DrTailMegakernelE4Function::default();
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(DR_TAIL_BLOCK_THREADS)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(context.get_exec_stream())
        .build();
    let args = DrTailMegakernelE4Arguments::new(desc);
    function.launch(&config, &args)
}

/// The CUDA implementation of the admission queries. Every call happens on the
/// scheduling thread, before any transfer is constructed.
pub(crate) struct DrTailCudaQueries {
    pub(crate) device_id: i32,
}

impl DrTailDeviceQueries for DrTailCudaQueries {
    fn attributes(&self) -> CudaResult<DrTailRawAttributes> {
        let function = DrTailMegakernelE4Function::default();
        let mut raw = std::mem::MaybeUninit::<era_cudart_sys::CudaFuncAttributes>::zeroed();
        // SAFETY: `raw` is a zeroed POD attribute record sized by the CUDA
        // headers, and the function pointer comes from the linked kernel.
        let status =
            unsafe { era_cudart_sys::cudaFuncGetAttributes(raw.as_mut_ptr(), function.as_ptr()) };
        if status != era_cudart_sys::CudaError::Success {
            return Err(status);
        }
        // SAFETY: the call above returned success, so the record is initialised.
        let raw = unsafe { raw.assume_init() };
        Ok(DrTailRawAttributes {
            static_smem_bytes: raw.sharedSizeBytes,
            local_bytes: raw.localSizeBytes,
            max_dynamic_smem_bytes: raw.maxDynamicSharedSizeBytes.max(0) as usize,
        })
    }

    fn device_optin_cap_bytes(&self) -> CudaResult<usize> {
        let cap = era_cudart::device::device_get_attribute(
            era_cudart_sys::CudaDeviceAttr::MaxSharedMemoryPerBlockOptin,
            self.device_id,
        )?;
        Ok(cap.max(0) as usize)
    }

    fn set_max_dynamic_smem_bytes(&self, bytes: usize) -> CudaResult<()> {
        let function = DrTailMegakernelE4Function::default();
        // SAFETY: the function pointer comes from the linked kernel and the
        // request was bounded against the device cap by the caller.
        let status = unsafe {
            cudaFuncSetAttribute(
                function.as_ptr(),
                CudaFuncAttribute::MaxDynamicSharedMemorySize,
                bytes as i32,
            )
        };
        if status != era_cudart_sys::CudaError::Success {
            return Err(status);
        }
        Ok(())
    }

    fn occupancy(&self, dynamic_smem_bytes: usize) -> CudaResult<u32> {
        let function = DrTailMegakernelE4Function::default();
        max_active_blocks_per_multiprocessor(
            &function,
            DR_TAIL_OCCUPANCY_THREADS as i32,
            dynamic_smem_bytes,
        )
        .map(|blocks| blocks.max(0) as u32)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn cpu_dr_tail_shared_eq_sizes_matches_helper_and_mutation_oracle() {
        use crate::backward::{make_eq_sizes, GkrEqSizes, GKR_EQ_GROUP_SIZE, GKR_EQ_HIGH_SLOTS};

        fn shared_initialization(challenge_count: usize) -> GkrEqSizes {
            let groups = challenge_count.div_ceil(GKR_EQ_GROUP_SIZE);
            let mut sizes = GkrEqSizes::zeroed();
            let mut consumed = 0;
            let mut high_idx = 0;
            for group in 0..groups {
                let remaining = challenge_count - consumed;
                let group_size = remaining.min(GKR_EQ_GROUP_SIZE) as u32;
                if group + 1 == groups {
                    sizes.low = group_size;
                } else {
                    assert!(high_idx < GKR_EQ_HIGH_SLOTS);
                    sizes.high[high_idx] = group_size;
                    high_idx += 1;
                }
                consumed += group_size as usize;
            }
            sizes
        }

        fn modulo_mutation(challenge_count: usize) -> GkrEqSizes {
            let mut sizes = GkrEqSizes::zeroed();
            sizes.low = (challenge_count % GKR_EQ_GROUP_SIZE) as u32;
            sizes
        }

        for challenge_count in [0, 1, 7, 8, 9, 16, 17, 24] {
            assert_eq!(
                shared_initialization(challenge_count),
                make_eq_sizes(challenge_count),
                "shared initialization drift at challenge_count={challenge_count}"
            );
        }
        for challenge_count in [8, 16, 24] {
            assert_ne!(
                modulo_mutation(challenge_count),
                make_eq_sizes(challenge_count),
                "the divisible-count mutation must be caught at challenge_count={challenge_count}"
            );
        }
    }
}
