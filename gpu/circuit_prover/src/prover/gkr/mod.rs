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

/// The VM programs a proof will run, compiled before any work is enqueued.
///
/// Empty unless a switch selects a coordinate. Held by value and handed to the
/// passes that need it — see [`compile_selected_vm_programs`] for why neither is
/// looked up again downstream.
pub(crate) struct GkrVmPrograms {
    /// The forward interpreter program, when `AB_GKR_FWD_VM_LAYERS` names layers.
    pub(crate) forward: Option<&'static forward::vm::program::CompiledCircuit>,
    /// One compiled slice per selected `(layer, regime)`, in selection order.
    pub(crate) backward: Vec<(
        backward::vm::coords::BwdVmCoord,
        &'static backward::vm::production_program::CompiledSlice,
    )>,
}

/// Compile every SELECTED VM program up front, and stop a selection the programs
/// cannot serve.
///
/// Called at the TOP of `prove()` for two reasons, both structural.
///
/// **Timing.** Compilation used to happen lazily inside the passes, and the
/// backward side's first hit was inside `into_main_layer_backward_state` — after
/// the forward pass and the dimension-reducing layers were already on the stream.
/// A cold compile there blocks the scheduling thread while the device drains,
/// which is the one thing `prove()` must never do (see
/// `docs/gpu_scheduling_contract.md`: it is enqueue-only, and the host's job is to
/// stay ahead). add_sub's coordinates are ~1.4 ms in release, but the corpus
/// projection (`report_the_compile_time_projection_over_the_corpus`) measures
/// blake2_with_extended_control's at 131 ms — most of a proof. Here nothing is
/// enqueued and the device is idle by definition.
///
/// **Ownership.** The programs are RETURNED, not left in a cache for the passes to
/// find. A pass that looks a program up needs the circuit identity to look it up
/// BY, and it does not have one; handing the compiled programs down instead means
/// no downstream code can pick up a program compiled for a different circuit. The
/// caches behind this function are keyed by [`CircuitType`] as well, so both the
/// producer and the store are safe for a process that proves more than one
/// circuit.
///
/// A wrong-circuit selection stops here. The forward pass has its own loud check;
/// the backward side had none, and would have bound a coordinate lowered from
/// another circuit's DAG.
pub(crate) fn compile_selected_vm_programs(
    circuit_type: crate::witness::circuit_type::CircuitType,
    artifact: &crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF>,
    is_add_sub: bool,
) -> GkrVmPrograms {
    let forward_layers = forward::path::vm_layers_from_env();
    let backward_coords = backward::vm::coords::coords_from_env();
    if forward_layers.is_empty() && backward_coords.is_empty() {
        return GkrVmPrograms {
            forward: None,
            backward: Vec::new(),
        };
    }
    assert!(
        is_add_sub,
        "{} / {} select a VM path but the circuit is not add_sub_lui_auipc_mop; both the \
         forward program and the backward coordinates are add_sub-specific",
        forward::path::AB_GKR_FWD_VM_LAYERS_ENV,
        backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV,
    );
    let forward = (!forward_layers.is_empty()).then(|| {
        forward::vm::program::compiled_program(circuit_type, artifact)
            .unwrap_or_else(|error| panic!("forward VM program: {error}"))
    });
    let backward = backward_coords
        .into_iter()
        .map(|coord| {
            let slice = backward::vm::production_program::compiled_slice(
                circuit_type,
                artifact,
                coord.layer,
                coord.regime,
            )
            .unwrap_or_else(|error| panic!("backward VM coordinate compile for {coord}: {error}"));
            (coord, slice)
        })
        .collect();
    GkrVmPrograms { forward, backward }
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
