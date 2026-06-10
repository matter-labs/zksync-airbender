//! A/B switch: replace the layer-0 GKR forward computation for the
//! `add_sub_lui_auipc_mop` circuit (cached layout) with a single pre-generated
//! fused CUDA kernel.
//!
//! Enabled via the `AB_GKR_FWD_GENERATED_LAYER0` env var (truthy = `1`/`true`).
//! When enabled the kernel is launched only for the add_sub-with-cached-layout
//! circuit; any other circuit panics (the kernel is add_sub-specific).
//!
//! The kernel produces the COMPLETE layer-0 output in one launch: the layer-0
//! caches (`Cached{layer:0, offset}`) and the layer-1 inner gate outputs
//! (`InnerLayer{layer:1, offset}`). The forward scheduler therefore SKIPS the
//! normal `schedule_cache_relations` / materialized-lookup-input /
//! `build_flat_forward_plan` path for layer 0 when this path runs.
//!
//! Numeric parity against the CPU prover's `forward_loop::evaluate_layer` is
//! validated by `prover::tests::generated_forward_layer0_matches_cpu_evaluate_layer_real_witness`;
//! end-to-end proof parity is validated by
//! `run_basic_unrolled_proof_job_multi_schedule_test`.

use std::sync::OnceLock;

use era_cudart::result::CudaResult;

use super::super::setup::GpuGKRForwardSetup;
use super::super::GpuGKRStorage;
use super::kernels::generated::{
    launch_generated_add_sub_layer0, GpuGkrFwdProxy, PERM_CHALLENGE_SLOTS,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{SetByRef, SetByVal};
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::gkr_address_audit::AddressClass;
use crate::prover::gkr::storage_layout::FieldType;
use crate::prover::ProverContext;
use crate::upstream::{
    Field, FieldExtension, GKRAddress, GKRCircuitArtifact, GKRExternalChallenges,
    GKRLayerDescription, NoFieldGKRRelation, NUM_PERMUTATION_ARGUMENT_KEY_PARTS,
};

/// Env var name for the A/B switch.
pub(crate) const AB_GKR_FWD_GENERATED_LAYER0_ENV: &str = "AB_GKR_FWD_GENERATED_LAYER0";

/// Whether the generated-layer0 A/B switch is enabled. Read once.
pub(crate) fn generated_layer0_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| match std::env::var(AB_GKR_FWD_GENERATED_LAYER0_ENV) {
        Ok(value) => {
            let v = value.trim().to_ascii_lowercase();
            v == "1" || v == "true"
        }
        Err(_) => false,
    })
}

/// Storage layer holding layer-0 caches (`Cached{0,..}` → `cache_{base,ext}`).
const CACHE_STORAGE_LAYER: usize = 0;
/// Storage layer holding layer-0 gate outputs (`InnerLayer{1,..}` →
/// `out_{base,ext}`); a layer-0 gate writes its output to layer 1.
const INNER_STORAGE_LAYER: usize = 1;

/// Returns true iff the (normalized) compiled circuit is the
/// `add_sub_lui_auipc_mop` circuit with a cached layout. The generated kernel
/// is specific to this circuit + layout; the cached layout is the one that
/// carries cached relations at layer 0 (the `has_decoder_lookup` path, not the
/// no-caches variant).
///
/// `is_add_sub` is threaded down from the proof orchestration where the
/// `CircuitType` is known; here we additionally confirm the cached layout from
/// the compiled artifact (`has_decoder_lookup` and a non-empty layer-0
/// `cached_relations`).
pub(crate) fn is_add_sub_cached_layout(
    is_add_sub: bool,
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> bool {
    is_add_sub
        && compiled_circuit.has_decoder_lookup
        && compiled_circuit
            .layers
            .first()
            .is_some_and(|layer| !layer.cached_relations.is_empty())
}

/// Build the forward-generation-specific challenge data carried in the kernel
/// proxy (previously uploaded to `__constant__`): the permutation linearization
/// challenges and additive seed are host-known at scheduling time, so they ride
/// by value; the decoder fill value is device-computed in `forward_setup`, so a
/// pointer to it is read directly. This replaces the prior 2×H2D + 1×D2D copies.
///
/// The shared `ab_gkr_lookup_alpha_powers` / `ab_gkr_lookup_gamma_consts`
/// `__constant__` tables are populated by the production setup + forward
/// preludes before this point and are still read from `__constant__`.
fn generated_challenge_proxy_fields<E>(
    external_challenges: &GKRExternalChallenges<BF, E4>,
    forward_setup: &GpuGKRForwardSetup<E>,
) -> ([E4; PERM_CHALLENGE_SLOTS], E4, *const E4)
where
    E: Field + FieldExtension<BF>,
{
    // perm_challenges[0..6] = linearization challenges; slots 6,7 stay zero.
    let mut perm_challenges = [E4::ZERO; PERM_CHALLENGE_SLOTS];
    debug_assert_eq!(NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1, 6);
    assert!(
        external_challenges
            .permutation_argument_linearization_challenges
            .len()
            <= PERM_CHALLENGE_SLOTS,
        "permutation linearization challenges exceed perm-challenge proxy slots"
    );
    for (slot, challenge) in perm_challenges.iter_mut().zip(
        external_challenges
            .permutation_argument_linearization_challenges
            .iter(),
    ) {
        *slot = *challenge;
    }
    let perm_additive = external_challenges.permutation_argument_additive_part;

    // Device-resident fill value computed by the forward setup. The pointer is
    // read on padding rows by the kernel; `forward_setup` (and thus the backing
    // allocation) outlives the stream-ordered launch scheduled by the caller.
    // `E == E4` in the only production monomorphization (asserted by the caller).
    let decoder_fill_value =
        forward_setup.decoder_lookup_fill_value_device().as_ptr() as *const E4;

    (perm_challenges, perm_additive, decoder_fill_value)
}

/// Allocate the consolidated views for every output address in the
/// `(storage_layer, class, FieldType::Ext)` slot, register them in storage so
/// the rest of the pipeline resolves them, and return the slot's consolidated
/// backing base pointer (the `poly_idx == 0` column) for the kernel proxy.
///
/// Returns `None` when the slot is absent for this circuit/layout (e.g. a
/// no-cache layout has no `cache_*` caches, or a circuit emits no base inner
/// outputs). The generator emits no `STORE_*` for an absent slot, so the proxy
/// pointer for it is never dereferenced.
///
/// The backing is one column-major matrix (`stride == trace_len`, dense
/// `poly_idx`), and the generated kernel writes column `poly_idx`, so passing
/// this base pointer makes the kernel write directly into the backing the rest
/// of the pipeline reads — no scratch, no scatter.
fn materialize_ext_output_slot<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    storage_layer: usize,
    class: AddressClass,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<Option<*mut E4>>
where
    E: Field + FieldExtension<BF> + 'static,
{
    let layout = storage.layout.as_ref().expect("storage layout required").clone();
    let addrs: Vec<GKRAddress> = match layout.layers.get(storage_layer) {
        Some(layer_layout) => layer_layout
            .index
            .iter()
            .filter(|(_, (c, f, _))| *c == class && *f == FieldType::Ext)
            .map(|(addr, _)| *addr)
            .collect(),
        None => Vec::new(),
    };
    if addrs.is_empty() {
        return Ok(None);
    }
    for addr in &addrs {
        let view = storage.allocate_ext_view(storage_layer, *addr, context)?;
        debug_assert_eq!(view.len(), trace_len, "ext output {addr:?} view length");
        storage.insert_extension_at_layer(storage_layer, *addr, view);
    }
    // All addresses in the slot share one consolidated backing; `as_ptr()` is
    // its column-0 base. `E == E4` in production (asserted by the caller).
    let base = storage.layers[storage_layer]
        .ext_class_backings
        .get(&class)
        .expect("ext backing was allocated by allocate_ext_view")
        .as_ptr() as *mut E4;
    Ok(Some(base))
}

/// Base-field analogue of [`materialize_ext_output_slot`] (e.g. base caches and
/// base inner outputs). Returns the `cache_base` / `out_base` proxy pointer.
fn materialize_base_output_slot<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    storage_layer: usize,
    class: AddressClass,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<Option<*mut BF>>
where
    E: Field + FieldExtension<BF> + 'static,
{
    let layout = storage.layout.as_ref().expect("storage layout required").clone();
    let addrs: Vec<GKRAddress> = match layout.layers.get(storage_layer) {
        Some(layer_layout) => layer_layout
            .index
            .iter()
            .filter(|(_, (c, f, _))| *c == class && *f == FieldType::Base)
            .map(|(addr, _)| *addr)
            .collect(),
        None => Vec::new(),
    };
    if addrs.is_empty() {
        return Ok(None);
    }
    for addr in &addrs {
        let view = storage.allocate_base_view(storage_layer, *addr, context)?;
        debug_assert_eq!(view.len(), trace_len, "base output {addr:?} view length");
        storage.insert_base_field_at_layer(storage_layer, *addr, view);
    }
    let base = storage.layers[storage_layer]
        .base_class_backings
        .get(&class)
        .expect("base backing was allocated by allocate_base_view")
        .as_ptr() as *mut BF;
    Ok(Some(base))
}

/// Schedule the generated fused layer-0 forward kernel so it writes its outputs
/// directly into the prover's consolidated per-`(layer, class, field)` storage
/// backings, fully replacing the normal layer-0 cache + gate scheduling.
///
/// The kernel stores each output at its storage-layout `poly_idx` (see the
/// generator's `emit_layer_forward`), and the four proxy output pointers
/// (`cache_{base,ext}` at layer 0, `out_{base,ext}` at layer 1) are the base
/// pointers of those four consolidated backings — so there is no intermediate
/// scratch and no D2D scatter. Slots a circuit/layout doesn't use are `None`
/// and take a harmless 1-element placeholder (the kernel never stores there).
///
/// Preconditions (checked by the caller `schedule_layer`): `layer_idx == 0`,
/// the A/B switch is enabled, and the circuit is add_sub-with-cached-layout.
/// The shared lookup-challenge `__constant__` tables and the input trace
/// holders are already populated/bound on `exec_stream` before this call.
#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_generated_layer0<E>(
    layer: &GKRLayerDescription,
    storage: &mut GpuGKRStorage<BF, E>,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + FieldExtension<BF> + SetByRef + SetByVal + 'static,
{
    // The kernel ABI is E4-specific (`ab_gkr_forward_add_sub_lui_auipc_mop_layer0_kernel`
    // takes `GpuGkrFwdProxy<E4>`). Production only runs the E4 monomorphization;
    // the generic `E` here is the forward storage field, which is E4 in that path.
    assert_eq!(
        std::mem::size_of::<E>(),
        std::mem::size_of::<E4>(),
        "generated layer-0 kernel is E4-specific"
    );

    // SAFETY: production runs only the E4 monomorphization (asserted above), so
    // `E == E4` and `GKRExternalChallenges<BF, E>` is layout-identical to
    // `GKRExternalChallenges<BF, E4>`. The reinterpret mirrors the validated
    // test wiring, which reads these same fields as E4.
    let external_challenges_e4: &GKRExternalChallenges<BF, E4> =
        unsafe { &*(external_challenges as *const _ as *const GKRExternalChallenges<BF, E4>) };

    // 1. Build the forward-generation-specific challenge data carried in the
    //    proxy (no H2D/D2D): perm challenges + additive by value, fill-value ptr.
    let (perm_challenges, perm_additive, decoder_fill_value) =
        generated_challenge_proxy_fields(external_challenges_e4, forward_setup);

    // 2. Materialize the four output backings from the storage layout (caches at
    //    layer 0, inner gate outputs at layer 1) and register their views, so
    //    downstream sumcheck / dimension reduction finds them. Each call returns
    //    the consolidated backing base pointer the kernel writes into directly.
    let cache_ext = materialize_ext_output_slot(
        storage,
        CACHE_STORAGE_LAYER,
        AddressClass::ThisLayerCachedWrite,
        trace_len,
        context,
    )?;
    let cache_base = materialize_base_output_slot(
        storage,
        CACHE_STORAGE_LAYER,
        AddressClass::ThisLayerCachedWrite,
        trace_len,
        context,
    )?;
    let out_ext = materialize_ext_output_slot(
        storage,
        INNER_STORAGE_LAYER,
        AddressClass::ThisLayerInnerLayerWrite,
        trace_len,
        context,
    )?;
    let out_base = materialize_base_output_slot(
        storage,
        INNER_STORAGE_LAYER,
        AddressClass::ThisLayerInnerLayerWrite,
        trace_len,
        context,
    )?;

    // 3. Placeholders for any absent output slot. The generated kernel emits no
    //    `STORE_*` for a slot the layout doesn't have, so these are never
    //    dereferenced — they only keep the proxy pointers non-null.
    let mut placeholder_ext: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top)?;
    let mut placeholder_base: DeviceAllocation<BF> = context.alloc(1, AllocationPlacement::Top)?;

    // Input pointers: memory / witness columns are the consolidated trace-holder
    // backings bound into storage at layer 0 (column-major, stride = trace_len;
    // column c at backing + c*trace_len). `setup` is never read at layer 0, so we
    // reuse the memory base pointer as a harmless non-null placeholder.
    let memory_ptr = storage
        .get_base_layer(GKRAddress::BaseLayerMemory(0))
        .as_ptr();
    let witness_ptr = storage
        .get_base_layer(GKRAddress::BaseLayerWitness(0))
        .as_ptr();
    let setup_ptr = memory_ptr; // unused by this circuit's layer-0 body

    let (generic_lookup_ptr, generic_lookup_len): (*const E4, u32) =
        if forward_setup.generic_lookup_len() > 0 {
            (
                forward_setup.generic_lookup().as_ptr() as *const E4,
                forward_setup.generic_lookup_len() as u32,
            )
        } else {
            (std::ptr::null(), 0)
        };

    let proxy = GpuGkrFwdProxy::<E4> {
        memory: memory_ptr,
        witness: witness_ptr,
        setup: setup_ptr,
        generic_lookup: generic_lookup_ptr,
        generic_lookup_len,
        cache_base: cache_base.unwrap_or_else(|| placeholder_base.as_mut_ptr()),
        cache_ext: cache_ext.unwrap_or_else(|| placeholder_ext.as_mut_ptr()),
        out_base: out_base.unwrap_or_else(|| placeholder_base.as_mut_ptr()),
        out_ext: out_ext.unwrap_or_else(|| placeholder_ext.as_mut_ptr()),
        trace_len: trace_len as u32,
        perm_challenges,
        perm_additive,
        decoder_fill_value,
    };

    // 4. Launch the fused kernel (one thread per row). It writes each output at
    //    its `poly_idx` column directly into the consolidated backing above.
    launch_generated_add_sub_layer0(proxy, trace_len, context)?;

    // 5. Replicate the pure copy-aliases that the generated kernel does NOT
    //     produce. `CopyInBaseField` / `CopyInExtensionField` gates do no
    //     arithmetic — the output `InnerLayer{1, off}` simply aliases its input
    //     poly (a memory column or a layer-0 cache). The normal path handles
    //     these as `aliased_*_outputs` in `commit_flat_forward_plan`; here we do
    //     the same registration so downstream resolves them. Must run AFTER the
    //     caches above are registered (offset 20 aliases `Cached{0,13}`).
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                assert_eq!(
                    gate.output_layer, 1,
                    "layer-0 copy gate must output to layer 1"
                );
                let GKRAddress::InnerLayer {
                    layer: out_layer,
                    offset: _,
                } = *output
                else {
                    panic!("copy gate output must be an InnerLayer address, got {output:?}");
                };
                let base_source = storage.try_get_base_poly(*input).map(|p| p.clone_shared());
                if let Some(source) = base_source {
                    storage.insert_base_field_at_layer(out_layer, *output, source);
                } else {
                    let ext_source = storage.get_ext_poly(*input).clone_shared();
                    storage.insert_extension_at_layer(out_layer, *output, ext_source);
                }
            }
            _ => {}
        }
    }

    // 6. Drop the absent-slot placeholders on exec_stream. The kernel launch
    //    (which embedded their raw pointers in the proxy) has already been
    //    scheduled above, so a stream-ordered drop here is safe per the lifetime
    //    contract. The real output backings live in `storage` and outlive this.
    drop(placeholder_ext);
    drop(placeholder_base);

    Ok(())
}
