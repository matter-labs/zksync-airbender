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
/// DAG lowering, validation, and all three symbolic compilers run once alongside
/// the circuit's other precomputations, off the proving path. The caller owns the
/// resulting programs; no process-global cache or search is involved.
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
    r0: Option<gpu_gkr_compiler::R0ProgramBundle>,
    continuations: Option<gpu_gkr_compiler::ContinuationProgramBundle>,
}

/// The empty set, for paths that run no VM: test harnesses that drive the
/// backward state directly, and any circuit `vm_circuit_name` does not admit.
/// A `static` rather than a `Default::default()` per caller so those paths can
/// borrow for `'static` and keep the state's lifetime parameter trivial.
static EMPTY_VM_PROGRAMS: GkrVmPrograms = GkrVmPrograms {
    forward: None,
    r0: None,
    continuations: None,
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
    /// `backward::vm::production_program::compile_all`.
    pub fn compile(
        circuit_type: crate::witness::circuit_type::CircuitType,
        artifact: &crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF>,
    ) -> Self {
        let dag = crate::upstream::lower_dag(artifact)
            .unwrap_or_else(|error| panic!("GKR DAG lowering: {error}"));
        crate::upstream::validate_dag(&dag)
            .unwrap_or_else(|error| panic!("GKR DAG validation: {error}"));
        let forward = Some(
            forward::vm::program::compile_program(circuit_type, &dag)
                .unwrap_or_else(|error| panic!("forward VM program: {error}")),
        );
        let backward = backward::vm::production_program::compile_all(&dag)
            .unwrap_or_else(|error| panic!("backward VM programs: {error}"));
        Self {
            forward,
            r0: Some(backward.r0),
            continuations: Some(backward.continuations),
        }
    }

    pub(crate) fn forward(&self) -> Option<&forward::vm::program::CompiledCircuit> {
        self.forward.as_ref()
    }

    pub(crate) fn r0_layer(&self, layer: usize) -> Option<&gpu_gkr_compiler::R0LayerProgram> {
        self.r0.as_ref()?.layers.get(layer)
    }

    pub(crate) fn continuation_layer(
        &self,
        layer: usize,
    ) -> Option<&gpu_gkr_compiler::ContinuationLayerProgram> {
        self.continuations.as_ref()?.layers.get(layer)
    }

    pub(crate) fn has_backward_coord(&self, coord: backward::vm::coords::BwdVmCoord) -> bool {
        match coord.regime {
            crate::upstream::BwdRegime::R0 => self.r0_layer(coord.layer).is_some(),
            crate::upstream::BwdRegime::Ext => self.continuation_layer(coord.layer).is_some(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.forward.is_none() && self.r0.is_none() && self.continuations.is_none()
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
    // EXPLICIT selections only. An unset switch now means "whatever this circuit
    // compiled", which is servable by construction and needs no check; what this
    // function exists to catch is an operator naming something the circuit cannot
    // run, and only an explicit value can do that.
    let forward_layers = forward::path::vm_layers_from_env().unwrap_or_default();
    let backward_coords = backward::vm::coords::coords_from_env().unwrap_or_default();
    if forward_layers.is_empty() && backward_coords.is_empty() {
        return;
    }
    assert!(
        !programs.is_empty(),
        "{} / {} select a VM path but {circuit_type:?} has no compiled VM programs; \
         no VM precomputation was supplied",
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
            programs.has_backward_coord(coord),
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
