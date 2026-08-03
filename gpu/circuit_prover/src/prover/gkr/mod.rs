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

/// Compile every SELECTED VM program before any work is enqueued, and stop a
/// selection the programs cannot serve.
///
/// Both program caches are lazy, and the backward one is first hit inside
/// `into_main_layer_backward_state` — which runs AFTER the forward pass and the
/// dimension-reducing layers are already on the stream. A cold compile there
/// blocks the scheduling thread while the device drains its queue, which is the
/// one thing `prove()` must never do (see `docs/gpu_scheduling_contract.md`: it
/// is enqueue-only, and the host's job is to stay ahead). add_sub's coordinates
/// are ~1.4 ms in release, but the corpus projection
/// (`report_the_compile_time_projection_over_the_corpus`) measures
/// blake2_with_extended_control's at 131 ms — most of a proof.
///
/// Called at the TOP of `prove()`, where nothing is enqueued and the device is
/// idle by definition, so the same host time costs the first proof some latency
/// and no proof its overlap. Later proofs in the process hit warm caches.
///
/// It is also where a wrong-circuit selection stops. The forward pass has its own
/// loud check; the backward side had none, and its compile would have bound a
/// coordinate lowered from a different circuit's DAG. Neither program cache is
/// keyed by circuit, so this check is what keeps that from mattering while
/// add_sub is the only allowlisted circuit — a second one needs the key, not just
/// the check.
pub(crate) fn warm_vm_program_caches(
    artifact: &crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF>,
    is_add_sub: bool,
) {
    let forward_layers = forward::path::vm_layers_from_env();
    let backward_coords = backward::vm::coords::coords_from_env();
    if forward_layers.is_empty() && backward_coords.is_empty() {
        return;
    }
    assert!(
        is_add_sub,
        "{} / {} select a VM path but the circuit is not add_sub_lui_auipc_mop; both the \
         forward program and the backward coordinates are add_sub-specific",
        forward::path::AB_GKR_FWD_VM_LAYERS_ENV,
        backward::vm::coords::AB_GKR_BWD_VM_COORDS_ENV,
    );
    // Errors are deliberately dropped: they are CACHED, so the real call site
    // still fails with the same message. Warming changes when the work happens,
    // never whether it succeeds.
    if !forward_layers.is_empty() {
        let _ = forward::vm::program::compiled_program(artifact);
    }
    for coord in backward_coords {
        let _ = backward::vm::production_program::compiled_slice(artifact, coord.layer, coord.regime);
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
