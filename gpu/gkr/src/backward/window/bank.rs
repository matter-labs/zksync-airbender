//! Binds window coefficient banks and final publications.

use std::collections::BTreeMap;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{ContinuationLayerProgram, WindowFamily, WindowProgram};
use gpu_prover_context::ProverContext;

use super::coefficient_bank::{
    build_continuation_coefficient_bank, build_window_coefficient_bank,
    schedule_bwd_coeff_bank_fill, CoefficientBankChunks, BWD_COEFF_CHALLENGE_CLAIM_BATCHING,
    BWD_COEFF_CHALLENGE_LOOKUP_ADDITIVE, BWD_COEFF_CHALLENGE_LOOKUP_MULTIPLICATIVE,
    BWD_COEFF_CHALLENGE_PERM_LINEARIZATION_BASE, BWD_COEFF_CHALLENGE_SLOTS,
};
use super::state::bwd_coeff_bank_device_ptr;
use crate::backward::main_continuation::repoint_final_evaluations_from_raw;
use crate::backward::{record_active_eq_slot_fold, GkrEqSizes};
use crate::upstream::{GKRAddress, ReadPlace, VirtualSetupKind, VirtualSetupPoly};

const MAIN_FINAL_EVALUATION_ELEMENTS_PER_ADDRESS: usize = 2;

pub(crate) fn family_read_place(family: WindowFamily, column: usize) -> Option<ReadPlace> {
    match family {
        WindowFamily::BaseLayerMemory => Some(ReadPlace::BaseLayerMemory { column }),
        WindowFamily::BaseLayerWitness => Some(ReadPlace::BaseLayerWitness { column }),
        WindowFamily::Setup => Some(ReadPlace::Setup { column }),
        WindowFamily::Scratch => Some(ReadPlace::Scratch { slot: column }),
        WindowFamily::LayerOutput { layer, .. } => Some(ReadPlace::LayerOutput {
            layer,
            offset: column,
        }),
        WindowFamily::CacheOutput { layer, .. } => Some(ReadPlace::CacheOutput {
            layer,
            offset: column,
        }),
        WindowFamily::VirtualSetup { .. } => None,
    }
}

pub(crate) fn virtual_setup_poly_address(kind: VirtualSetupKind) -> GKRAddress {
    GKRAddress::VirtualSetup(match kind {
        VirtualSetupKind::RangeCheck16Bits => VirtualSetupPoly::RangeCheck16Bits,
        VirtualSetupKind::RangeCheckTimestamp => VirtualSetupPoly::RangeCheckTimestamp,
        VirtualSetupKind::InitsAndTeardownsLow => VirtualSetupPoly::InitsAndTeardownsLow,
        VirtualSetupKind::InitsAndTeardownsHigh => VirtualSetupPoly::InitsAndTeardownsHigh,
    })
}

pub(crate) fn drained_eq_sizes(mut eq_sizes: GkrEqSizes, rounds: u8) -> GkrEqSizes {
    for _ in 0..rounds {
        record_active_eq_slot_fold(&mut eq_sizes);
    }
    eq_sizes
}

fn schedule_challenge_slab(
    slab: &mut DeviceAllocation<E4>,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let stream = context.get_exec_stream();
    let prefix = BWD_COEFF_CHALLENGE_LOOKUP_MULTIPLICATIVE as usize;
    debug_assert_eq!(BWD_COEFF_CHALLENGE_PERM_LINEARIZATION_BASE, 0);
    // SAFETY: all pointers refer to device allocations with the copied lengths.
    unsafe {
        memory_copy_async(
            &mut slab[..prefix],
            DeviceSlice::from_raw_parts(external_challenges, prefix),
            stream,
        )?;
        for (slot, source) in [
            (
                BWD_COEFF_CHALLENGE_LOOKUP_MULTIPLICATIVE,
                lookup_multiplicative,
            ),
            (BWD_COEFF_CHALLENGE_LOOKUP_ADDITIVE, lookup_additive),
            (BWD_COEFF_CHALLENGE_CLAIM_BATCHING, claim_batching),
        ] {
            let slot = slot as usize;
            memory_copy_async(
                &mut slab[slot..slot + 1],
                DeviceSlice::from_raw_parts(source, 1),
                stream,
            )?;
        }
    }
    Ok(())
}

pub(crate) struct MainContinuationCoefficientBank {
    final_evaluations: BTreeMap<GKRAddress, usize>,
    chunks: CoefficientBankChunks,
    slab: DeviceAllocation<E4>,
}

pub(crate) fn prepare_main_continuation_coefficient_bank(
    program: &ContinuationLayerProgram,
    inits_and_teardowns_top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<MainContinuationCoefficientBank> {
    let blob = build_continuation_coefficient_bank(
        &program.coefficient_recipes,
        inits_and_teardowns_top_bits,
    )
    .unwrap_or_else(|error| panic!("continuation coefficient bank translation: {error:?}"));
    Ok(MainContinuationCoefficientBank {
        final_evaluations: BTreeMap::new(),
        chunks: CoefficientBankChunks::build(&blob),
        slab: context.alloc(BWD_COEFF_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?,
    })
}

fn build_canonical_final_evaluation_offsets(
    addresses: impl IntoIterator<Item = (usize, GKRAddress)>,
) -> Result<BTreeMap<GKRAddress, usize>, &'static str> {
    let mut offsets = BTreeMap::new();
    for (column, address) in addresses {
        let byte_offset = column
            .checked_mul(MAIN_FINAL_EVALUATION_ELEMENTS_PER_ADDRESS)
            .and_then(|elements| elements.checked_mul(size_of::<E4>()))
            .ok_or("canonical final-evaluation byte offset overflowed")?;
        if offsets.insert(address, byte_offset).is_some() {
            return Err("duplicate canonical final-evaluation address");
        }
    }
    Ok(offsets)
}

fn repoint_final_evaluations<E>(
    allocation: &DeviceAllocation<E4>,
    byte_offsets: &BTreeMap<GKRAddress, usize>,
    destinations: &mut BTreeMap<GKRAddress, *const E>,
) {
    let allocation_bytes = allocation
        .len()
        .checked_mul(size_of::<E4>())
        .expect("the final-evaluation allocation byte length must fit usize");
    repoint_final_evaluations_from_raw(
        allocation.as_ptr(),
        allocation_bytes,
        MAIN_FINAL_EVALUATION_ELEMENTS_PER_ADDRESS,
        byte_offsets,
        destinations,
    )
    .unwrap_or_else(|error| panic!("final-evaluation repoint: {error:?}"));
}

impl MainContinuationCoefficientBank {
    pub(crate) fn set_external_final_evaluation_offsets(
        &mut self,
        addresses: impl IntoIterator<Item = (usize, GKRAddress)>,
    ) -> Result<(), &'static str> {
        self.final_evaluations = build_canonical_final_evaluation_offsets(addresses)?;
        Ok(())
    }

    pub(crate) fn repoint_final_evaluations_from_external_buffer<E>(
        &self,
        buffer: &DeviceAllocation<E4>,
        destinations: &mut BTreeMap<GKRAddress, *const E>,
    ) {
        repoint_final_evaluations(buffer, &self.final_evaluations, destinations);
    }
}

pub(crate) fn schedule_main_continuation_coefficient_bank_fill(
    launch: &mut MainContinuationCoefficientBank,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    schedule_challenge_slab(
        &mut launch.slab,
        external_challenges,
        lookup_multiplicative,
        lookup_additive,
        claim_batching,
        context,
    )?;
    schedule_bwd_coeff_bank_fill(
        &launch.chunks,
        launch.slab.as_ptr(),
        bwd_coeff_bank_device_ptr(),
        context.get_exec_stream(),
    )?;
    Ok(())
}

pub(crate) struct WindowCoefficientBank {
    chunks: CoefficientBankChunks,
    slab: DeviceAllocation<E4>,
}

pub(crate) fn prepare_window_coefficient_bank(
    program: &WindowProgram,
    inits_and_teardowns_top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<WindowCoefficientBank> {
    let blob =
        build_window_coefficient_bank(&program.coefficient_plans, inits_and_teardowns_top_bits)
            .unwrap_or_else(|error| panic!("window coefficient bank translation: {error:?}"));
    Ok(WindowCoefficientBank {
        chunks: CoefficientBankChunks::build(&blob),
        slab: context.alloc(BWD_COEFF_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?,
    })
}

pub(crate) fn schedule_window_coefficient_bank_fill(
    bank: &mut WindowCoefficientBank,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    schedule_challenge_slab(
        &mut bank.slab,
        external_challenges,
        lookup_multiplicative,
        lookup_additive,
        claim_batching,
        context,
    )?;
    schedule_bwd_coeff_bank_fill(
        &bank.chunks,
        bank.slab.as_ptr(),
        bwd_coeff_bank_device_ptr(),
        context.get_exec_stream(),
    )?;
    Ok(())
}

#[cfg(test)]
pub(crate) fn final_evaluation_repoint_probe(
    allocation_bytes: usize,
    elements_per_address: usize,
    byte_offsets: &BTreeMap<GKRAddress, usize>,
    addresses: impl IntoIterator<Item = GKRAddress>,
) -> Result<BTreeMap<GKRAddress, usize>, String> {
    let base = 0x10_000usize as *const E4;
    let mut destinations: BTreeMap<GKRAddress, *const E4> = addresses
        .into_iter()
        .map(|address| (address, std::ptr::null()))
        .collect();
    repoint_final_evaluations_from_raw(
        base,
        allocation_bytes,
        elements_per_address,
        byte_offsets,
        &mut destinations,
    )
    .map_err(|error| format!("{error:?}"))?;
    Ok(destinations
        .into_iter()
        .map(|(address, pointer)| (address, pointer as usize - base as usize))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_final_offsets_are_checked_and_unique() {
        let a = GKRAddress::BaseLayerWitness(0);
        let b = GKRAddress::BaseLayerMemory(2);
        let offsets = build_canonical_final_evaluation_offsets([(0, a), (1, b)]).unwrap();
        assert_eq!(offsets[&a], 0);
        assert_eq!(offsets[&b], 2 * size_of::<E4>());
        assert_eq!(
            build_canonical_final_evaluation_offsets([(0, a), (1, a)]),
            Err("duplicate canonical final-evaluation address")
        );
        assert_eq!(
            build_canonical_final_evaluation_offsets([(usize::MAX, a)]),
            Err("canonical final-evaluation byte offset overflowed")
        );
    }
}
