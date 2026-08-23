use core::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

use super::capacity::DrTailCapacityDecision;

const CUDA_SOURCE: &str = include_str!("../../../native/gkr/backward/dr_tail_megakernel.cu");
const CUDA_HEADER: &str = include_str!("../../../native/gkr/backward/dr_tail_megakernel.cuh");

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
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 0 * size_of::<*const E4>() == 16);
    assert!(offset_of!(DrTailMegakernelDesc, source_ptrs) + 1 * size_of::<*const E4>() == 24);
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
    DrTailMegakernelE4,
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

pub(crate) fn launch_dr_tail_megakernel_e4(
    desc: DrTailMegakernelDesc,
    capacity: &DrTailCapacityDecision,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_capacity_matches_descriptor(&desc, capacity);
    let dynamic_smem_bytes = capacity.dynamic_smem_bytes;
    assert!(dynamic_smem_bytes <= i32::MAX as usize);

    let function = DrTailMegakernelE4Function::default();
    // Opt in to the exact dynamic allocation already admitted by the capacity decision.
    unsafe {
        cudaFuncSetAttribute(
            function.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            dynamic_smem_bytes as i32,
        )
    }
    .wrap()?;
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(DR_TAIL_BLOCK_THREADS)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(context.get_exec_stream())
        .build();
    let args = DrTailMegakernelE4Arguments::new(desc);
    function.launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_dr_tail_abi_layout_and_kernel_argument_ceiling() {
        assert_eq!(gpu_gkr_compiler::KERNEL_ARGUMENT_CEILING_BYTES, 32_764);
        assert_eq!(size_of::<DrTailSlot>(), 8);
        assert_eq!(align_of::<DrTailSlot>(), 2);
        assert_eq!(size_of::<DrTailMegakernelDesc>(), 192);
        assert_eq!(align_of::<DrTailMegakernelDesc>(), 8);
        assert!(size_of::<DrTailMegakernelDesc>() <= CUDA_KERNEL_ARGUMENT_CEILING_BYTES);
        assert_eq!(
            1usize << (DR_TAIL_MAX_REMAINING_ROUNDS - 1),
            DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE
        );
        assert_eq!(
            2 * DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE,
            DR_TAIL_BLOCK_THREADS as usize
        );
        assert!(CUDA_HEADER.contains("sizeof(gkr_dr_tail_megakernel_desc) == 192"));
        assert!(CUDA_HEADER.contains("sizeof(gkr_dr_tail_megakernel_desc) <= 32764"));
        assert!(CUDA_HEADER.contains("GKR_DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE = 128"));
    }

    #[test]
    fn cpu_dr_tail_source_guard() {
        let sources = [CUDA_SOURCE, CUDA_HEADER];
        assert!(CUDA_SOURCE.contains("#include \"dr_tail_megakernel.cuh\""));
        assert!(CUDA_SOURCE.contains("ab_gkr_dr_tail_megakernel_e4_kernel"));
        assert!(CUDA_HEADER.contains("ab_gkr_dim_reducing_batch_challenge_table"));
        for forbidden in [
            "ab_gkr_eq_high",
            "ab_gkr_dim_reducing_layer_claim_point",
            "gkr_dim_reducing_continuation_batched_compact_inner",
        ] {
            assert!(
                sources.iter().all(|source| !source.contains(forbidden)),
                "DR-tail production source names prohibited symbol/helper {forbidden}"
            );
        }
    }
}
