//! Binding the forward VM's lowering inputs to the production prover state.
//!
//! # The derived-E4 census for add_sub layer 0
//!
//! The compiled layer sources seven derived-E4 slots, and where each may live
//! is decided by whether the *host* knows its value at scheduling time:
//!
//! | Channel | n | Refs (all `power: One`) | Runtime source |
//! |---|---|---|---|
//! | `ArgDerivedE4` | 6 | `PermutationAdditive`, `PermutationLinearization` × {AddressLow, TimestampLow, TimestampHigh, ValueLow, ValueHigh} | `GKRExternalChallenges` — an INPUT to `prove()`, host-filled once at `ExternalChallengesTransfer::new` |
//! | `ConstDerivedE4` | 1 (+1 fill) | `LookupAdditive`; plus the decoder fill appended at `fill_bank_idx` | `GpuGKRForwardSetup::lookup_additive_part_device()` and `decoder_lookup_fill_value_device()` — DEVICE-resident, never on the host |
//!
//! So the permutation challenges are schedule-time known and correctly ride
//! [`FwdVmDesc`] by value — the same values `generated_layer0` already passes
//! by value in its kernel proxy. The two `ConstDerivedE4` slots are not, and
//! [`upload_const_derived_e4`](super::upload_const_derived_e4) cannot supply
//! them: it takes `&[E4]` host values, and the host has neither number.
//!
//! Both device values are `power: One`, i.e. straight reads of an existing
//! device scalar with no arithmetic, so the fill is two 16-byte **D2D** copies
//! into the `__constant__` bank through its device address — the mechanism
//! `lower_layer_desc`'s own doc names for exactly this case, and the same one
//! `bwd_seg_coeff_bank_device_ptr` uses on the backward side. Anything that is
//! not a plain `power: One` device scalar is a hard error: a future circuit
//! that needs a real evaluation must fail loudly, not copy a wrong value.
//!
//! # Storage residency
//!
//! Destination views are allocated lazily as each flat layer is built and
//! registered at commit, so at the top of the pass L0's outputs do not exist.
//! `generated_layer0` has the identical problem — it also replaces L0's flat
//! scheduling wholesale — and solves it with
//! `materialize_{ext,base}_output_slot`. This module calls those, rather than
//! growing a second copy.

use std::ffi::c_void;
use std::ptr::{null, null_mut};
use std::sync::OnceLock;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart_sys::cudaGetSymbolAddress;
use gkr_eval_isa::fwd::context::CompiledLayer;
use gkr_eval_isa::fwd::isa::LdcSub;

use super::desc::{CONST_DERIVED_E4_CAP, FILL_BANK_NONE};
use super::lower::{FwdVmHeaderInputs, FwdVmLayerSetup, ResolvedColumn};
use super::{ab_gkr_fwd_vm_const_derived_e4, lower::lower_layer_desc};
use crate::prover::gkr::forward::generated_layer0::{
    materialize_base_output_slot, materialize_ext_output_slot, register_layer_copy_aliases,
};
use crate::prover::gkr::gkr_address_audit::AddressClass;
use crate::prover::gkr::setup::GpuGKRForwardSetup;
use crate::prover::gkr::stage1::GpuGKRStage1Output;
use crate::prover::gkr::GpuGKRStorage;
use crate::ops::simple::{set_by_val, SetByRef, SetByVal};
use crate::primitives::field::{BF, E4};
use crate::prover::ProverContext;
use crate::upstream::{
    ChallengeKey, ChallengePower, ChallengeRef, Field, FieldExtension, GKRAddress,
    GKRExternalChallenges, GKRLayerDescription, PermutationSlot,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};

/// The (storage layer, class) slots a VM layer writes.
///
/// Layer `L`'s caches are `Cached{L,..}` at storage layer `L`, and its gate
/// outputs are `InnerLayer{L+1,..}` at storage layer `L+1` — a gate writes its
/// output to the NEXT layer. Both fields of both slots, so a layer that has no
/// caches (add_sub L1-L3) or no base outputs (every layer above 0) simply
/// materializes nothing for that slot; `materialize_*_output_slot` returns
/// `None` for an empty address set.
pub(crate) fn materialized_slots(layer_idx: usize) -> [(usize, AddressClass); 2] {
    [
        (layer_idx, AddressClass::ThisLayerCachedWrite),
        (layer_idx + 1, AddressClass::ThisLayerInnerLayerWrite),
    ]
}

/// Which device scalar a `ConstDerivedE4` slot is a copy of.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ConstDerivedE4Source {
    /// `GpuGKRForwardSetup::lookup_additive_part_device()`.
    LookupAdditive,
}

#[derive(Debug)]
pub(crate) enum BindError {
    /// A `ConstDerivedE4` ref is not a plain `power: One` read of a device
    /// scalar the forward setup owns, so it cannot be filled by a copy.
    UnsupportedConstDerivedE4(ChallengeRef),
    /// An `ArgDerivedE4` ref is not host-known at scheduling time, so it
    /// cannot ride the by-value descriptor.
    NonScheduleTimeArgDerivedE4(ChallengeRef),
    /// The bank (real slots plus the appended decoder fill) exceeds the
    /// `__constant__` symbol.
    BankOverflow { n: usize },
    /// A bank copy failed.
    Cuda(era_cudart_sys::CudaError),
}

impl std::fmt::Display for BindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BindError::UnsupportedConstDerivedE4(r) => write!(
                f,
                "const-derived-E4 {r:?} is not a plain `power: One` read of a device scalar the \
                 forward setup owns; filling the bank by copy would write a wrong value"
            ),
            BindError::NonScheduleTimeArgDerivedE4(r) => write!(
                f,
                "arg-derived-E4 {r:?} is not known to the host at scheduling time, so it cannot \
                 ride the by-value descriptor"
            ),
            BindError::BankOverflow { n } => write!(
                f,
                "const-derived-E4 bank of {n} exceeds CONST_DERIVED_E4_CAP {CONST_DERIVED_E4_CAP}"
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
        _ => return Err(BindError::NonScheduleTimeArgDerivedE4(r.clone())),
    };
    Ok(match r.power {
        ChallengePower::One => base,
        ChallengePower::Static(p) => base.pow(p),
    })
}

/// Which device scalar fills a `ConstDerivedE4` slot, or why it cannot.
pub(crate) fn const_derived_e4_source(
    r: &ChallengeRef,
) -> Result<ConstDerivedE4Source, BindError> {
    match (&r.key, &r.power) {
        (ChallengeKey::LookupAdditive, ChallengePower::One) => {
            Ok(ConstDerivedE4Source::LookupAdditive)
        }
        _ => Err(BindError::UnsupportedConstDerivedE4(r.clone())),
    }
}

/// Device address of the `__constant__` derived-E4 bank, so it can be written
/// from device memory. `upload_const_derived_e4` reaches the same symbol for
/// host sources; this is the device-source route.
fn const_derived_e4_bank_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = null_mut();
        // SAFETY: the Rust static is the stub for the `__constant__`
        // `e4[CONST_DERIVED_E4_CAP]` bank `fwd_vm.cu` defines.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_fwd_vm_const_derived_e4 as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_fwd_vm_const_derived_e4");
        p as usize
    });
    ptr as *mut E4
}

/// Fill this layer's `ConstDerivedE4` bank **from device memory**, on
/// `exec_stream`, so no challenge value ever passes through the host.
///
/// Ordering contract (`lower_layer_desc`): every slot must be written before
/// any launch of this layer's descriptor. Both copies are enqueued on
/// `exec_stream`, and so is the launch, so the ordering is the stream's.
pub(crate) fn stage_const_derived_e4_bank<E>(
    cl: &CompiledLayer,
    setup: &FwdVmLayerSetup,
    forward_setup: &GpuGKRForwardSetup<E>,
    context: &ProverContext,
) -> Result<(), BindError> {
    let n = setup.desc.n_const_derived_e4 as usize;
    if n > CONST_DERIVED_E4_CAP {
        return Err(BindError::BankOverflow { n });
    }
    let bank = const_derived_e4_bank_device_ptr();
    let fill_idx = setup.desc.fill_bank_idx;

    for i in 0..n {
        if fill_idx != FILL_BANK_NONE && i as u32 == fill_idx {
            continue; // the appended decoder fill, handled below
        }
        let r = cl
            .ctx
            .derived_e4
            .get(LdcSub::ConstDerivedE4, i as u16)
            .expect("bank index below n_const_derived_e4 must resolve");
        let src: &DeviceSlice<E> = match const_derived_e4_source(r)? {
            ConstDerivedE4Source::LookupAdditive => forward_setup.lookup_additive_part_device(),
        };
        copy_one_e4_into_bank(bank, i, src, context).map_err(BindError::Cuda)?;
    }

    if fill_idx != FILL_BANK_NONE {
        let src = forward_setup.decoder_lookup_fill_value_device();
        copy_one_e4_into_bank(bank, fill_idx as usize, &src[..1], context)
            .map_err(BindError::Cuda)?;
    }
    Ok(())
}

/// One 16-byte D2D copy into bank slot `idx`.
fn copy_one_e4_into_bank<E>(
    bank: *mut E4,
    idx: usize,
    src: &DeviceSlice<E>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        size_of::<E>(),
        size_of::<E4>(),
        "the const-derived-E4 bank is E4-specific"
    );
    // SAFETY: `bank` is the device address of an `e4[CONST_DERIVED_E4_CAP]`
    // `__constant__` symbol and `idx < CONST_DERIVED_E4_CAP` (checked by the
    // caller against `n_const_derived_e4`), so `bank.add(idx)` is one valid
    // E4 slot. `src` is one device-resident E4 (size asserted above).
    let dst = unsafe { DeviceSlice::from_raw_parts_mut(bank.add(idx), 1) };
    let src = unsafe { DeviceSlice::from_raw_parts(src.as_ptr() as *const E4, 1) };
    memory_copy_async(dst, src, context.get_exec_stream())
}

/// Read the first `n` slots of the `__constant__` bank back to the host.
/// Test-only: the fill is a device-side write with no host mirror, so the gate
/// that compares it against an independent producer has to read it back.
#[cfg(test)]
pub(crate) fn read_const_derived_e4_bank(n: usize, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; n];
    // SAFETY: `n <= CONST_DERIVED_E4_CAP` slots of the bank symbol.
    let src = unsafe { DeviceSlice::from_raw_parts(const_derived_e4_bank_device_ptr(), n) };
    memory_copy_async(&mut host, src, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

/// One resolved storage column, through the production storage accessors.
///
/// This is the SAME resolution the flat path uses: `try_get_base_poly` /
/// `try_get_ext_poly` are production methods on `GpuGKRStorage`.
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
pub(crate) fn production_header<E>(
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    trace_len: usize,
) -> FwdVmHeaderInputs {
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
    }
}

/// Allocate and register every destination the VM writes for `layer_idx`.
///
/// The flat plan normally does this while building the layer; the VM replaces
/// that scheduling entirely, so nothing else would. Reuses
/// `generated_layer0`'s helpers over [`materialized_slots`] — the same slots
/// that path materializes for layer 0, generalized to layer L.
pub(crate) fn prepare_layer_destinations<E>(
    layer_idx: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + FieldExtension<BF> + SetByRef + SetByVal + 'static,
{
    for (layer, class) in materialized_slots(layer_idx) {
        let ext_base = materialize_ext_output_slot(storage, layer, class, trace_len, context)?;
        let base_base = materialize_base_output_slot(storage, layer, class, trace_len, context)?;

        // Poison every freshly materialized destination when the parity gate
        // asks for it. That gate runs in a process where earlier `#[serial]`
        // proofs have already filled and freed these very pool blocks, so a VM
        // that launches but writes nothing could reproduce the right proof from
        // recycled correct values. Poison makes that failure loud. `set_by_val`
        // is a stream-ordered launch on `exec_stream`, ahead of the VM launch —
        // no scheduling-thread dereference.
        //
        // Opt-in rather than automatic in test builds: it is ~36 full-length
        // column writes, which showed up as a ~3 ms per-proof cost charged to
        // the VM arm alone and silently inverted the first A/B result. A
        // correctness aid must not be inside the thing being measured.
        #[cfg(test)]
        if poison_destinations_enabled() {
            const POISON: u32 = 0x5EED_DEAD & 0x7FFF_FFFF;
            let stream = context.get_exec_stream();
            if let Some(base) = ext_base {
                let len = storage.layers[layer].ext_class_backings[&class].len();
                // SAFETY: `base` is the consolidated ext backing's column-0
                // pointer and `len` is that same allocation's length.
                let dst = unsafe { DeviceSlice::from_raw_parts_mut(base as *mut E, len) };
                set_by_val(E::from_base(BF::new(POISON)), dst, stream)?;
            }
            if let Some(base) = base_base {
                let len = storage.layers[layer].base_class_backings[&class].len();
                // SAFETY: as above, for the base-field backing.
                let dst = unsafe { DeviceSlice::from_raw_parts_mut(base, len) };
                set_by_val(BF::new(POISON), dst, stream)?;
            }
        }
        #[cfg(not(test))]
        {
            let _ = (ext_base, base_base);
        }
    }
    Ok(())
}

/// Whether [`prepare_layer0_destinations`] poisons what it materializes.
/// Off unless [`AB_GKR_FWD_VM_POISON_DESTINATIONS_ENV`] is truthy, so timing
/// runs do not pay for a correctness aid. Read fresh, like the layer switch.
#[cfg(test)]
pub(crate) fn poison_destinations_enabled() -> bool {
    std::env::var(AB_GKR_FWD_VM_POISON_DESTINATIONS_ENV)
        .map(|v| { let v = v.trim().to_ascii_lowercase(); v == "1" || v == "true" })
        .unwrap_or(false)
}

/// Env var enabling the destination poison (parity gates only, never timing).
#[cfg(test)]
pub(crate) const AB_GKR_FWD_VM_POISON_DESTINATIONS_ENV: &str =
    "AB_GKR_FWD_VM_POISON_DESTINATIONS";

/// Lower one layer against the production prover state.
#[allow(clippy::too_many_arguments)]
pub(crate) fn bind_layer<E>(
    cl: &CompiledLayer,
    storage: &GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    trace_len: usize,
    context: &ProverContext,
) -> Result<FwdVmLayerSetup, String>
where
    E: Copy,
{
    let header = production_header(stage1, forward_setup, trace_len);
    let resolve = |addr: GKRAddress| resolve_storage_column(storage, addr);
    // A resolution failure here surfaces as a lowering error naming the
    // address; `arg_derived_e4_value`'s own error is not plumbed through the
    // `&dyn Fn` closure signature, so it panics with the ref named — either
    // way it is a hard stop, never a zero.
    let challenge = |r: &ChallengeRef| {
        arg_derived_e4_value(external_challenges, r).unwrap_or_else(|e| panic!("{e}"))
    };
    lower_layer_desc(cl, &header, &resolve, &challenge, Some(context))
        .map_err(|e| format!("lower_layer_desc: {e:?}"))
}

/// Schedule one layer on the forward VM: materialize its destinations, lower
/// against production storage, fill the derived-E4 bank from device memory,
/// and launch — all on `exec_stream`, in that order.
///
/// The bank fill and the launch are both enqueued on `exec_stream`, which is
/// the ordering `lower_layer_desc`'s fill contract requires. `setup` owns any
/// `program_ldg` fallback the by-value descriptor points into and stays alive
/// until the launch has been *scheduled* — which is all the contract asks.
#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_vm_layer<E>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    cl: &CompiledLayer,
    budget_lanes: u32,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + FieldExtension<BF> + SetByRef + SetByVal + 'static,
{
    // The descriptor ABI and the `__constant__` bank are E4-specific, exactly
    // as `generated_layer0`'s kernel proxy is. Production only runs the E4
    // monomorphization; the generic `E` is the forward storage field.
    assert_eq!(
        size_of::<E>(),
        size_of::<E4>(),
        "the forward VM descriptor ABI is E4-specific"
    );
    // SAFETY: `E == E4` (asserted above), so `GKRExternalChallenges<BF, E>` is
    // layout-identical to `GKRExternalChallenges<BF, E4>`. Mirrors the same
    // reinterpret `schedule_generated_layer0` does for the same reason.
    let external_challenges: &GKRExternalChallenges<BF, E4> =
        unsafe { &*(external_challenges as *const _ as *const GKRExternalChallenges<BF, E4>) };

    prepare_layer_destinations(layer_idx, storage, trace_len, context)?;

    let setup = bind_layer(
        cl,
        storage,
        stage1,
        forward_setup,
        external_challenges,
        trace_len,
        context,
    )
    .unwrap_or_else(|e| panic!("forward VM layer {layer_idx}: {e}"));

    stage_const_derived_e4_bank(cl, &setup, forward_setup, context)
        .unwrap_or_else(|e| panic!("forward VM layer {layer_idx}: {e}"));

    super::launch_fwd_vm_s4(&setup, budget_lanes, context)?;

    // The VM emits no `GlobalMaterialize` for a pure copy gate — its output
    // aliases its input — so, exactly as `generated_layer0` must, register
    // those aliases here. Without this, layer 1 resolves nothing for
    // `InnerLayer{L+1, 0}`. After the launch, mirroring generated_layer0's
    // ordering: the aliases are host-side bookkeeping over already-registered
    // caches, not device work.
    register_layer_copy_aliases(layer_idx, layer, storage);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::upstream::{ChallengeKey, ChallengePower, ChallengeRef, PermutationSlot};

    /// The `ConstDerivedE4` fill is a straight 16-byte copy of a device scalar
    /// the forward setup already owns. That is only sound for `power: One`
    /// refs that map onto such a scalar; anything else needs a real evaluation
    /// and must fail loudly rather than copy a wrong number.
    #[test]
    fn a_const_derived_ref_that_is_not_a_plain_device_scalar_is_rejected() {
        assert!(const_derived_e4_source(&ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::Static(2),
        })
        .is_err());

        assert!(const_derived_e4_source(&ChallengeRef {
            key: ChallengeKey::ConstraintAggregation,
            power: ChallengePower::One,
        })
        .is_err());

        assert_eq!(
            const_derived_e4_source(&ChallengeRef {
                key: ChallengeKey::LookupAdditive,
                power: ChallengePower::One,
            })
            .unwrap(),
            ConstDerivedE4Source::LookupAdditive
        );
    }

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
