//! Binds compiled forward layers to prover storage and runtime challenge data.
//!
//! Host-known challenges ride in the descriptor. Device-resident constants
//! and the decoder fill are copied into the constant bank before launch.

use std::ffi::c_void;
use std::ptr::{null, null_mut};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart_sys::cudaGetSymbolAddress;
use gpu_gkr_compiler::{CompiledLayer, ForwardSpecialStrategy as SpecialStrategy};

use super::desc::FwdVmDesc;
use super::desc::CONST_DERIVED_E4_CAP;
use super::lower::{FwdVmHeaderInputs, FwdVmLowerError, ResolvedColumn};
use super::output::{materialize_output_slot, register_layer_copy_aliases};
use super::{ab_gkr_fwd_vm_const_derived_e4, lower::lower_layer_desc};
use crate::gkr_address_audit::AddressClass;
use crate::setup::GpuGKRForwardSetup;
use crate::stage1::GpuGKRStage1Output;
use crate::upstream::{
    ChallengeKey, ChallengePower, ChallengeRef, Field, GKRAddress, GKRExternalChallenges,
    GKRLayerDescription, PermutationSlot, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use crate::GpuGKRStorage;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

#[derive(Debug)]
pub(crate) enum BindError {
    /// An `ArgDerivedE4` ref is not host-known at scheduling time, so it
    /// cannot ride the by-value descriptor.
    NonScheduleTimeArgDerivedE4(ChallengeRef),
    /// A bank copy failed.
    Cuda(era_cudart_sys::CudaError),
}

impl std::fmt::Display for BindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BindError::NonScheduleTimeArgDerivedE4(r) => write!(
                f,
                "arg-derived-E4 {r:?} is not known to the host at scheduling time, so it cannot \
                 ride the by-value descriptor"
            ),
            BindError::Cuda(e) => write!(f, "const-derived-E4 bank copy failed: {e:?}"),
        }
    }
}

/// Map a `PermutationSlot` to its index in
/// `GKRExternalChallenges::permutation_argument_linearization_challenges`.
fn permutation_linearization_index(slot: &PermutationSlot) -> usize {
    match slot {
        PermutationSlot::AddressLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
        PermutationSlot::AddressHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
        PermutationSlot::TimestampLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
        PermutationSlot::TimestampHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
        PermutationSlot::ValueLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
        PermutationSlot::ValueHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    }
}

/// Resolve an `ArgDerivedE4` ref against the host-known external challenges.
///
/// Only the two permutation kinds are host-known; the lookup and aggregation
/// kinds live in device memory and must not reach a by-value field.
pub(crate) fn arg_derived_e4_value(
    external_challenges: &GKRExternalChallenges<BF, E4>,
    r: &ChallengeRef,
) -> Result<E4, BindError> {
    let base = match &r.key {
        ChallengeKey::PermutationAdditive => external_challenges.permutation_argument_additive_part,
        ChallengeKey::PermutationLinearization(slot) => {
            external_challenges.permutation_argument_linearization_challenges
                [permutation_linearization_index(slot)]
        }
        _ => return Err(BindError::NonScheduleTimeArgDerivedE4(*r)),
    };
    Ok(match r.power {
        ChallengePower::One => base,
        ChallengePower::Static(p) => base.pow(p),
    })
}

/// Device address of the derived-E4 constant bank.
fn const_derived_e4_bank_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = null_mut();
    // SAFETY: the Rust static is the stub for the `__constant__`
    // `e4[CONST_DERIVED_E4_CAP]` bank `fwd_vm.cu` defines.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_fwd_vm_const_derived_e4 as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_fwd_vm_const_derived_e4");
    ptr.cast()
}

/// Fill this layer's `ConstDerivedE4` bank **from device memory**, on
/// `exec_stream`, so no challenge value ever passes through the host.
///
/// Ordering contract (`lower_layer_desc`): every slot must be written before
/// any launch of this layer's descriptor. Both copies are enqueued on
/// `exec_stream`, and so is the launch, so the ordering is the stream's.
pub(crate) fn stage_const_derived_e4_bank(
    cl: &CompiledLayer,
    forward_setup: &GpuGKRForwardSetup,
    context: &ProverContext,
) -> Result<(), BindError> {
    let bank = const_derived_e4_bank_device_ptr();
    if cl.derived_e4.uses_lookup_additive() {
        let src = forward_setup.lookup_additive_part_device();
        copy_one_e4_into_bank(bank, 0, src, context).map_err(BindError::Cuda)?;
    }

    if cl
        .specials
        .iter()
        .any(|special| matches!(special, SpecialStrategy::PeekDecoder { .. }))
    {
        let src = forward_setup.decoder_lookup_fill_value_device();
        copy_one_e4_into_bank(bank, CONST_DERIVED_E4_CAP - 1, &src[..1], context)
            .map_err(BindError::Cuda)?;
    }
    Ok(())
}

/// One 16-byte D2D copy into bank slot `idx`.
fn copy_one_e4_into_bank(
    bank: *mut E4,
    idx: usize,
    src: &DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<()> {
    // SAFETY: `bank` is the device address of an `e4[CONST_DERIVED_E4_CAP]`
    // `__constant__` symbol and `idx < CONST_DERIVED_E4_CAP` (checked by the
    // caller against `CONST_DERIVED_E4_CAP`), so `bank.add(idx)` is one valid
    // E4 slot. `src` is one device-resident E4.
    let dst = unsafe { DeviceSlice::from_raw_parts_mut(bank.add(idx), 1) };
    memory_copy_async(dst, src, context.get_exec_stream())
}

/// One resolved storage column, through the production storage accessors.
///
/// Resolve a column through the production storage accessors.
pub(crate) fn resolve_storage_column<E>(
    storage: &GpuGKRStorage<BF, E>,
    addr: GKRAddress,
) -> Option<ResolvedColumn>
where
    E: Copy,
{
    if let Some(p) = storage.try_get_base_poly(addr) {
        return Some(ResolvedColumn {
            is_e4: false,
            ptr: p.as_ptr() as *const u8,
            matrix_base: p.backing.as_ptr() as *mut u8,
            stride_bytes: (p.len * size_of::<BF>()) as u32,
        });
    }
    storage.try_get_ext_poly(addr).map(|p| ResolvedColumn {
        is_e4: true,
        ptr: p.as_ptr() as *const u8,
        matrix_base: p.backing.as_ptr() as *mut u8,
        stride_bytes: (p.len * size_of::<E4>()) as u32,
    })
}

/// Per-layer header inputs from the production prover buffers: the three
/// stage-1 mapping arenas, the decoder mapping column, and the shared
/// α-folded generic-lookup table.
///
/// The generic-lookup table is released once no later layer needs it
/// (`release_forward_lookup_resources_after_layer`), so read it through the
/// length accessor, which reports 0 after release, rather than the panicking
/// one.
pub(crate) fn production_header<'a>(
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup,
    trace_len: usize,
    inits_and_teardowns_top_bits: &'a [u32],
) -> FwdVmHeaderInputs<'a> {
    let m = &stage1.lookup_mappings;
    assert_eq!(
        m.trace_len, trace_len,
        "mapping-arena column stride != trace_len"
    );
    let (table, table_len) = if forward_setup.generic_lookup_len() > 0 {
        (
            forward_setup.generic_lookup().as_ptr() as *const E4,
            forward_setup.generic_lookup_len() as u32,
        )
    } else {
        (null(), 0)
    };
    FwdVmHeaderInputs {
        mapping_arena: [
            if m.has_generic_family() {
                m.generic_family().as_ptr()
            } else {
                null()
            },
            if m.has_range_check_16() {
                m.range_check_16().as_ptr()
            } else {
                null()
            },
            if m.has_timestamp() {
                m.timestamp().as_ptr()
            } else {
                null()
            },
        ],
        decoder_mapping_col: m
            .has_decoder
            .then(|| u16::try_from(m.num_generic_sets).expect("num_generic_sets exceeds u16")),
        table,
        table_len,
        count: trace_len as u32,
        inits_and_teardowns_top_bits,
    }
}

pub(crate) fn prepare_layer_destinations(
    layer_idx: usize,
    storage: &mut GpuGKRStorage<BF, E4>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    for (layer, class) in [
        (layer_idx, AddressClass::ThisLayerCachedWrite),
        (layer_idx + 1, AddressClass::ThisLayerInnerLayerWrite),
    ] {
        materialize_output_slot(storage, layer, class, trace_len, context)?;
    }
    Ok(())
}

/// Lower one layer against the production prover state.
#[allow(clippy::too_many_arguments)]
pub(crate) fn bind_layer(
    cl: &CompiledLayer,
    storage: &GpuGKRStorage<BF, E4>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    trace_len: usize,
    inits_and_teardowns_top_bits: &[u32],
) -> Result<FwdVmDesc, FwdVmLowerError> {
    let header = production_header(
        stage1,
        forward_setup,
        trace_len,
        inits_and_teardowns_top_bits,
    );
    let resolve = |addr: GKRAddress| resolve_storage_column(storage, addr);
    // The infallible callback contract makes a missing challenge a hard error.
    let challenge = |r: &ChallengeRef| {
        arg_derived_e4_value(external_challenges, r).unwrap_or_else(|e| panic!("{e}"))
    };
    lower_layer_desc(cl, &header, &resolve, &challenge)
}

/// Materialize destinations, bind the descriptor, stage constants, and launch.
#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_vm_layer(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    cl: &CompiledLayer,
    storage: &mut GpuGKRStorage<BF, E4>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    trace_len: usize,
    inits_and_teardowns_top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<()> {
    prepare_layer_destinations(layer_idx, storage, trace_len, context)?;

    let setup = bind_layer(
        cl,
        storage,
        stage1,
        forward_setup,
        external_challenges,
        trace_len,
        inits_and_teardowns_top_bits,
    )
    .unwrap_or_else(|e| panic!("forward VM layer {layer_idx}: {e:?}"));

    stage_const_derived_e4_bank(cl, forward_setup, context)
        .unwrap_or_else(|e| panic!("forward VM layer {layer_idx}: {e}"));

    super::launch_fwd_vm(&setup, context)?;

    // Pure copy gates alias existing storage instead of materializing output.
    register_layer_copy_aliases(layer_idx, layer, storage);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::upstream::{ChallengeKey, ChallengePower, ChallengeRef, PermutationSlot};

    /// The permutation challenges ride the descriptor by value, so their
    /// mapping onto `GKRExternalChallenges` must match the upstream slot
    /// indices exactly — an off-by-one here is a wrong proof, not a crash.
    #[test]
    fn permutation_slots_map_to_the_upstream_linearization_indices() {
        for (slot, expected) in [
            (
                PermutationSlot::AddressLow,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
            ),
            (
                PermutationSlot::AddressHigh,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
            ),
            (
                PermutationSlot::TimestampLow,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
            ),
            (
                PermutationSlot::TimestampHigh,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
            ),
            (
                PermutationSlot::ValueLow,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
            ),
            (
                PermutationSlot::ValueHigh,
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
            ),
        ] {
            assert_eq!(permutation_linearization_index(&slot), expected);
        }
    }

    /// `ArgDerivedE4` is a by-value descriptor field, so every ref routed there
    /// must be resolvable on the host at scheduling time. add_sub L0 sources
    /// only permutation challenges, which are an input to `prove()`; a ref that
    /// is NOT host-known must be rejected rather than silently zeroed.
    #[test]
    fn an_arg_derived_ref_that_is_not_host_known_is_rejected() {
        let external = GKRExternalChallenges::<BF, E4> {
            permutation_argument_linearization_challenges: std::array::from_fn(|_| E4::ZERO),
            permutation_argument_additive_part: E4::ZERO,
            _marker: std::marker::PhantomData,
        };
        assert!(arg_derived_e4_value(
            &external,
            &ChallengeRef {
                key: ChallengeKey::LookupAdditive,
                power: ChallengePower::One,
            }
        )
        .is_err());
    }
}
