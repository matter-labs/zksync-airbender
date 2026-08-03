// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub(crate) mod backward;
pub(crate) mod base_layer_claims;
pub(crate) mod forward;
#[cfg(test)]
pub(crate) mod gkr_address_audit_helpers;
#[cfg(test)]
mod gpu_kernels;
pub mod setup;
pub(crate) mod stage1;
pub(crate) mod storage;
mod storage_types;
pub(crate) mod support;

pub(crate) use backward::kernels::BackwardKernels;
pub(crate) use forward::kernels::ForwardKernels;
pub(crate) use gpu_gkr_model::address_audit as gkr_address_audit;
pub(crate) use gpu_gkr_model::storage_layout;
pub(crate) use gpu_gkr_model::transform;
#[cfg(test)]
pub(crate) use gpu_kernels::GpuKernels;
pub(crate) use setup::kernels::SetupKernels;
pub(crate) use storage_types::*;
pub(crate) use support::eval_recipes;
pub(crate) use support::immediate_factors;
pub(crate) use support::initial_inner_products as gkr_initial_inner_products;

use std::ptr::null;
use std::sync::Arc;

/// A circuit's VM programs: per-circuit precomputation, owned by the caller.
///
/// # Why this is a plain owned structure
///
/// Compiling is the intensive part of running the VM — `lower_dag` + `validate`
/// over a layout that can be tens of megabytes, then one coordinate compile per
/// `(layer, regime)`. `report_the_compile_time_projection_over_the_corpus`
/// measures add_sub at ~2.7 ms and blake2_with_extended_control at ~143 ms. That
/// belongs where a circuit's other precomputations are built: once, off any
/// proving path, held by the caller. Not in a process-global cache behind a lock,
/// which would put the work on whichever thread happened to arrive first and give
/// `prove()` no way to know when it had been paid.
///
/// So `prove()` takes one of these by reference and hands borrows to the passes.
/// Nothing downstream compiles, looks anything up, or locks.
///
/// # Why it ignores the switches
///
/// The programs a circuit HAS are a property of the circuit; which ones a PROOF
/// runs is a property of `AB_GKR_FWD_VM_LAYERS` / `AB_GKR_BWD_VM_COORDS`, read at
/// plan build. Building them switch-independently is what lets one process
/// alternate arms — the A/B does exactly that — against a single compiled set.
#[derive(Default)]
pub struct GkrVmPrograms {
    /// The forward interpreter program, when this circuit has an embedded
    /// schedule (`forward::vm::program::embedded_schedule`).
    forward: Option<forward::vm::program::CompiledCircuit>,
    /// Every `(layer, regime)` coordinate of the circuit's main layers.
    backward: Vec<(
        backward::vm::coords::BwdVmCoord,
        backward::vm::production_program::CompiledSlice,
    )>,
}

/// The empty set, for paths that run no VM: test harnesses that drive the
/// backward state directly, and any circuit `vm_circuit_name` does not admit.
/// A `static` rather than a `Default::default()` per caller so those paths can
/// borrow for `'static` and keep the state's lifetime parameter trivial.
static EMPTY_VM_PROGRAMS: GkrVmPrograms = GkrVmPrograms {
    forward: None,
    backward: Vec::new(),
};

impl GkrVmPrograms {
    pub(crate) fn empty() -> &'static Self {
        &EMPTY_VM_PROGRAMS
    }

    /// Compile everything the VM can run for this circuit. Empty for a circuit the
    /// VM does not support, which costs nothing.
    ///
    /// `artifact` must be the RAW one, before
    /// `transform::normalize_compiled_circuit_for_gpu` — see
    /// `backward::vm::production_program::compile_all_slices`.
    pub fn compile(
        circuit_type: crate::witness::circuit_type::CircuitType,
        artifact: &crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF>,
    ) -> Self {
        let Some(circuit_name) = vm_circuit_name(circuit_type) else {
            return Self::default();
        };
        let forward = forward::vm::program::compile_program(circuit_type, artifact)
            .map(|result| result.unwrap_or_else(|error| panic!("forward VM program: {error}")));
        let backward = backward::vm::production_program::compile_all_slices(circuit_name, artifact)
            .unwrap_or_else(|error| panic!("backward VM coordinates: {error}"));
        Self { forward, backward }
    }

    pub(crate) fn forward(&self) -> Option<&forward::vm::program::CompiledCircuit> {
        self.forward.as_ref()
    }

    /// The compiled slice for one coordinate, or `None` if this circuit has none.
    pub(crate) fn backward_slice(
        &self,
        coord: backward::vm::coords::BwdVmCoord,
    ) -> Option<&backward::vm::production_program::CompiledSlice> {
        self.backward
            .iter()
            .find_map(|(selected, slice)| (*selected == coord).then_some(slice))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.forward.is_none() && self.backward.is_empty()
    }
}

/// The name the VM's lean compiler records for a circuit, and the VM's allowlist:
/// `None` means no VM path exists for it and none may be selected.
///
/// Deliberately a hard match rather than a structural predicate — a circuit the VM
/// has never been measured on must be added here on purpose.
pub(crate) fn vm_circuit_name(
    circuit_type: crate::witness::circuit_type::CircuitType,
) -> Option<&'static str> {
    use crate::witness::circuit_type::{
        CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
    };
    match circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => Some("add_sub_lui_auipc_mop"),
        // The layout `Blake2WithCompression` proves is
        // `blake2_with_extended_control` — see the fixture that loads it.
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            Some("blake2_with_extended_control")
        }
        _ => None,
    }
}

/// Reject a VM selection this circuit's compiled programs cannot serve.
///
/// Called by `prove()` before the first enqueue, so a switch set for the wrong
/// circuit stops there rather than reaching a binder built for another layout.
pub(crate) fn check_vm_selection_is_servable(
    programs: &GkrVmPrograms,
    circuit_type: crate::witness::circuit_type::CircuitType,
) {
    let forward_layers = forward::path::vm_layers_from_env();
    let backward_coords = backward::vm::coords::coords_from_env();
    if forward_layers.is_empty() && backward_coords.is_empty() {
        return;
    }
    assert!(
        !programs.is_empty(),
        "{} / {} select a VM path but {circuit_type:?} has no compiled VM programs; \
         `gkr::vm_circuit_name` is the allowlist",
        forward::path::AB_GKR_FWD_VM_LAYERS_ENV,
        backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV,
    );
    if !forward_layers.is_empty() {
        assert!(
            programs.forward.is_some(),
            "{} selects layers but {circuit_type:?} has no embedded forward schedule",
            forward::path::AB_GKR_FWD_VM_LAYERS_ENV,
        );
    }
    for coord in backward_coords {
        assert!(
            programs.backward_slice(coord).is_some(),
            "{} selects {coord}, which {circuit_type:?} has no compiled coordinate for",
            backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV,
        );
    }
}

use crate::prover::gkr::storage_layout::GpuGKRStorageLayout;
use crate::upstream::GKRAddress;

#[cfg(test)]
pub(crate) use tests::{
    GpuSumcheckRound0DeviceLaunchDescriptors, GpuSumcheckRound0HostLaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1ScheduledLaunchDescriptors,
};

impl<B, E> GpuGKRStorage<B, E> {
    /// Attach a pre-computed storage layout. Subsequent
    /// `allocate_base_view` / `allocate_ext_view` calls will route allocations
    /// through the per-class consolidated backings indexed by this layout.
    pub(crate) fn set_layout(&mut self, layout: Arc<GpuGKRStorageLayout>) {
        assert!(self.layout.is_none(), "layout already set");
        self.layout = Some(layout);
    }

    fn base_trace_len(&self) -> usize {
        self.layers
            .first()
            .and_then(|layer| {
                layer
                    .base_field_inputs
                    .values()
                    .map(GpuBaseFieldPoly::len)
                    .max()
            })
            .expect("layer 0 must contain at least one real base-field polynomial")
    }

    fn base_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => Some(0),
        }
    }

    fn ext_poly_layer(address: GKRAddress) -> Option<usize> {
        match address {
            GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => Some(layer),
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => None,
        }
    }

    fn get_base_poly_for_address(&self, address: GKRAddress) -> Option<&GpuBaseFieldPoly<B>> {
        let layer = Self::base_poly_layer(address)?;
        self.layers.get(layer)?.base_field_inputs.get(&address)
    }

    fn get_ext_poly_for_address(&self, address: GKRAddress) -> Option<&GpuExtensionFieldPoly<E>> {
        let layer = Self::ext_poly_layer(address)?;
        self.layers.get(layer)?.extension_field_inputs.get(&address)
    }

    fn get_base_source_for_round_0(&self, address: GKRAddress) -> GpuBaseFieldPolySource<B> {
        if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(address) {
            return GpuBaseFieldPolySource {
                start: null(),
                next_layer_size: self.base_trace_len() / 2,
                source_kind,
            };
        }

        let layer = match address {
            GKRAddress::Cached { layer, .. } | GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => 0,
        };
        let source = self.layers[layer]
            .base_field_inputs
            .get(&address)
            .unwrap_or_else(|| {
                panic!(
                    "Polynomial with address {:?} is missing from input sources for base field polys",
                    address
                )
            });
        source.accessor()
    }

    #[cfg(test)]
    pub(crate) fn get_base_layer_mem(&self, offset: usize) -> &GpuBaseFieldPoly<B> {
        self.get_base_poly_for_address(GKRAddress::BaseLayerMemory(offset))
            .expect("base layer memory poly must exist")
    }

    pub(crate) fn get_base_layer(&self, address: GKRAddress) -> &GpuBaseFieldPoly<B> {
        self.get_base_poly_for_address(address)
            .expect("base layer poly must exist")
    }

    pub(crate) fn try_get_base_poly(&self, address: GKRAddress) -> Option<&GpuBaseFieldPoly<B>> {
        self.get_base_poly_for_address(address)
    }

    pub(crate) fn try_get_ext_poly(
        &self,
        address: GKRAddress,
    ) -> Option<&GpuExtensionFieldPoly<E>> {
        self.get_ext_poly_for_address(address)
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.layers.truncate(layer + 1);
    }

    pub(crate) fn get_ext_poly(&self, address: GKRAddress) -> &GpuExtensionFieldPoly<E> {
        self.get_ext_poly_for_address(address)
            .unwrap_or_else(|| panic!("extension poly must exist for {address:?}"))
    }

    pub(crate) fn insert_base_field_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: GpuBaseFieldPoly<B>,
    ) {
        if layer >= self.layers.len() {
            self.layers
                .resize_with(layer + 1, GpuGKRLayerSource::default);
        }
        let existing = self.layers[layer].base_field_inputs.insert(address, value);
        assert!(
            existing.is_none(),
            "trying to insert another value for layer {}, address {:?}",
            layer,
            address
        );
    }

    pub(crate) fn insert_extension_at_layer(
        &mut self,
        layer: usize,
        address: GKRAddress,
        value: GpuExtensionFieldPoly<E>,
    ) {
        if layer >= self.layers.len() {
            self.layers
                .resize_with(layer + 1, GpuGKRLayerSource::default);
        }
        let existing = self.layers[layer]
            .extension_field_inputs
            .insert(address, value);
        assert!(
            existing.is_none(),
            "trying to insert another value for layer {}, address {:?}",
            layer,
            address
        );
    }
}

#[cfg(test)]
pub(crate) mod tests;
