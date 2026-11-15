use core::mem::{align_of, offset_of, size_of};

use era_cudart::{cuda_kernel, result::CudaResult};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

use crate::{
    baby_bear::backward::dr_tail::capacity::DrTailCapacityDecision,
    backward::dr_tail::{
        kernels::*,
        resources::{DrTailRawAttributes, DR_TAIL_OCCUPANCY_THREADS},
    },
};

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
    assert!(
        size_of::<DrTailMegakernelDesc>() + size_of::<*mut E4>()
            <= CUDA_KERNEL_ARGUMENT_CEILING_BYTES
    );
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
    ab_gkr_dr_tail_megakernel_e4_kernel(desc: DrTailMegakernelDesc, global_state: *mut E4,)
);

fn assert_capacity_matches_descriptor(
    desc: &DrTailMegakernelDesc,
    capacity: &DrTailCapacityDecision,
) {
    let folding_steps = desc.folding_steps as usize;
    let entry_round = desc.entry_round as usize;
    let source_count = desc.source_count as usize;
    assert_eq!(entry_round, capacity.entry_round);
    let remaining_rounds = folding_steps.checked_sub(entry_round).unwrap();
    assert!((1..=DR_TAIL_MAX_REMAINING_ROUNDS).contains(&remaining_rounds));
    let first_round_acc_size = 1usize << (remaining_rounds - 1);
    assert!(first_round_acc_size <= DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE);
    assert!((1..=DR_TAIL_MAX_SOURCES).contains(&source_count));
    for source in desc.source_ptrs.iter().take(source_count) {
        assert_eq!(
            *source as usize % 32,
            0,
            "DR-tail packed entry load requires 32-byte aligned canonical source pointers",
        );
    }
    assert!((1usize << remaining_rounds) <= DR_TAIL_BLOCK_THREADS as usize);
}

/// Caller contract: `DrTailResources::capacity` has raised the kernel-wide
/// dynamic shared memory ceiling to cover this launch.
pub(crate) fn launch_dr_tail_megakernel_e4(
    desc: DrTailMegakernelDesc,
    capacity: &DrTailCapacityDecision,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_capacity_matches_descriptor(&desc, capacity);
    launch_dr_tail_state::<E4, _, _>(
        capacity.global_state_bytes,
        capacity.dynamic_smem_bytes,
        DR_TAIL_BLOCK_THREADS,
        &DrTailMegakernelE4Function::default(),
        |state| DrTailMegakernelE4Arguments::new(desc, state),
        context,
    )
}

/// Attribute queries against the linked DR-tail kernel, made while scheduling
/// the DR tail.
pub(crate) fn dr_tail_attributes() -> CudaResult<DrTailRawAttributes> {
    kernel_attributes(&DrTailMegakernelE4Function::default())
}

pub(crate) fn set_dr_tail_max_dynamic_smem_bytes(bytes: usize) -> CudaResult<()> {
    set_kernel_max_dynamic_smem(&DrTailMegakernelE4Function::default(), bytes)
}

pub(crate) fn dr_tail_occupancy(dynamic_smem_bytes: usize) -> CudaResult<u32> {
    kernel_occupancy(
        &DrTailMegakernelE4Function::default(),
        DR_TAIL_OCCUPANCY_THREADS,
        dynamic_smem_bytes,
    )
}

#[cfg(test)]
pub(crate) mod tests {
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
