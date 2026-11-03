//! Device-resource admission for the DR-tail launcher.
//!
//! This module deliberately keeps the resource record separate from
//! `GkrPrograms`: attributes are device- and launch-configuration-specific and
//! must be queried on the scheduling thread for each proof admission.
//!
//! `maxDynamicSharedSizeBytes` is kernel-wide mutable state. Admission never
//! lowers it because an earlier proof may still be waiting to enqueue a launch
//! that needs the current ceiling.

use std::collections::BTreeSet;

use super::capacity::{select_capacity, DrTailCapacityDecision, DrTailCapacityRequest};
use crate::backward::derive_dimension_reducing_inputs;
use crate::backward::main_layer::blueprints::build_dimension_reducing_slots_static;
use crate::storage_layout::GpuGKRStorageLayout;
use crate::upstream::{GKRAddress, GKRCircuitArtifact, PrimeField};
use crate::DrWindowProgramBundle;
use era_cudart::result::CudaResult;

struct DrTailLayerInput {
    layer_idx: usize,
    folding_steps: usize,
    canonical_sources: Vec<GKRAddress>,
}

fn dr_tail_layer_inputs<F: PrimeField>(
    artifact: &GKRCircuitArtifact<F>,
    final_trace_log_2: usize,
) -> Vec<DrTailLayerInput> {
    let trace_log = artifact.trace_len.trailing_zeros() as usize;
    let layout = GpuGKRStorageLayout::from_artifact_with_tower(artifact, final_trace_log_2);
    derive_dimension_reducing_inputs(
        artifact.layers.len(),
        &artifact.global_output_map,
        trace_log as u32,
        final_trace_log_2 as u32,
    )
    .into_iter()
    .map(|(layer_idx, layer)| {
        let layer_offset = layer_idx - artifact.layers.len();
        let folding_steps = trace_log
            .checked_sub(layer_offset)
            .and_then(|value| value.checked_sub(1))
            .expect("DR folding width underflowed");
        let slots = build_dimension_reducing_slots_static(&layer);
        let canonical_sources = slots
            .input_addresses()
            .map(|address| layout.aliases.get(&address).copied().unwrap_or(address))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        DrTailLayerInput {
            layer_idx,
            folding_steps,
            canonical_sources,
        }
    })
    .collect()
}

/// Threads per DR-tail block; occupancy is queried at exactly this width.
pub(crate) const DR_TAIL_OCCUPANCY_THREADS: u32 = super::kernels::DR_TAIL_BLOCK_THREADS;

/// Raw linked-kernel attributes, as reported by `cudaFuncGetAttributes`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailRawAttributes {
    pub static_smem_bytes: usize,
    pub local_bytes: usize,
    /// The kernel's current dynamic opt-in ceiling.
    pub max_dynamic_smem_bytes: usize,
}

/// Continuation windows the layer lands before the recursive tail entry.
pub(crate) fn dr_continuation_window_count(entry_round: usize) -> usize {
    if entry_round == 0 {
        return 0;
    }
    debug_assert!(entry_round >= 3 && entry_round.is_multiple_of(3));
    (entry_round - 3) / 3
}

/// A per-proof plan. Its fields are private and the only constructor is
/// [`admit_dr_tail_resources`], so a plan handed to `prove()` cannot have
/// skipped admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrTailProofPlan {
    device_id: i32,
    static_smem_bytes: usize,
    device_cap_bytes: usize,
    layers: Vec<DrTailLayerPlan>,
    window_programs: DrWindowProgramBundle,
}

impl DrTailProofPlan {
    pub(crate) fn layers(&self) -> &[DrTailLayerPlan] {
        &self.layers
    }

    /// DR programs compiled for this proof's geometry.
    pub(crate) fn window_programs(&self) -> &DrWindowProgramBundle {
        &self.window_programs
    }

    /// Recomputes the admitted plan before enqueueing any work. The admitted
    /// capacities are device-specific, so the scheduling device must still be
    /// the one admission ran on.
    pub fn validate_before_enqueue(
        &self,
        programs: &crate::GkrPrograms,
        final_trace_log_2: u32,
        context: &gpu_prover_context::ProverContext,
    ) {
        let current = era_cudart::device::get_device()
            .expect("DR-tail enqueue must observe the scheduling device");
        assert_eq!(
            current,
            context.get_device_id(),
            "proof scheduling must run on the context device"
        );
        assert_eq!(
            context.get_device_id(),
            self.device_id,
            "DR-tail plan was admitted on another device"
        );
        let expected = plan_dr_tail_layers(
            programs.runtime_circuit().as_ref(),
            final_trace_log_2 as usize,
            self.static_smem_bytes,
            self.device_cap_bytes,
        );
        assert_eq!(self.layers, expected);
    }
}

/// One admitted capacity bound to its artifact layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DrTailLayerPlan {
    layer_idx: usize,
    folding_steps: usize,
    canonical_sources: Vec<GKRAddress>,
    capacity: DrTailCapacityDecision,
}

impl DrTailLayerPlan {
    pub(crate) const fn layer_idx(&self) -> usize {
        self.layer_idx
    }

    pub(crate) const fn capacity(&self) -> DrTailCapacityDecision {
        self.capacity
    }
}

/// Runtime cursor shared by production scheduling and host-only identity
/// tests. Binding is by absolute layer key; execution order is irrelevant.
pub(crate) struct DrTailPlanCursor<'a> {
    layers: &'a [DrTailLayerPlan],
    consumed: BTreeSet<usize>,
}

impl<'a> DrTailPlanCursor<'a> {
    pub(crate) fn new(layers: &'a [DrTailLayerPlan]) -> Self {
        Self {
            layers,
            consumed: BTreeSet::new(),
        }
    }

    pub(crate) fn bind(
        &mut self,
        layer_idx: usize,
        folding_steps: usize,
        canonical_sources: &[GKRAddress],
    ) -> DrTailCapacityDecision {
        let planned = self
            .layers
            .iter()
            .find(|planned| planned.layer_idx == layer_idx)
            .expect("DR-tail plan is missing a layer");
        assert_eq!(planned.folding_steps, folding_steps);
        assert_eq!(planned.canonical_sources, canonical_sources);
        assert!(self.consumed.insert(layer_idx));
        planned.capacity
    }

    pub(crate) fn finish(self) {
        assert_eq!(self.consumed.len(), self.layers.len());
    }
}

pub(crate) fn plan_dr_tail_layers<F: PrimeField>(
    artifact: &GKRCircuitArtifact<F>,
    final_trace_log_2: usize,
    static_smem_bytes: usize,
    device_cap_bytes: usize,
) -> Vec<DrTailLayerPlan> {
    let inputs = dr_tail_layer_inputs(artifact, final_trace_log_2);
    assert!(!inputs.is_empty());
    inputs
        .into_iter()
        .map(|input| {
            let canonical_sources = input.canonical_sources;
            let capacity = select_capacity(DrTailCapacityRequest {
                folding_steps: input.folding_steps,
                canonical_sources: canonical_sources.len(),
                static_smem_bytes,
                device_cap_bytes,
            });
            DrTailLayerPlan {
                layer_idx: input.layer_idx,
                folding_steps: input.folding_steps,
                canonical_sources,
                capacity,
            }
        })
        .collect()
}

pub(crate) fn admit_dr_tail_resources<F: PrimeField>(
    device_id: i32,
    artifact: &GKRCircuitArtifact<F>,
    final_trace_log_2: usize,
    window_programs: DrWindowProgramBundle,
) -> CudaResult<DrTailProofPlan> {
    assert_eq!(
        era_cudart::device::get_device()?,
        device_id,
        "DR-tail admission must run on the requested device"
    );
    let attributes = super::kernels::dr_tail_attributes()?;
    assert_eq!(
        attributes.local_bytes, 0,
        "DR-tail kernel spills to local memory"
    );
    let device_cap_bytes = super::kernels::dr_tail_device_optin_cap_bytes(device_id)?;

    let layers = plan_dr_tail_layers(
        artifact,
        final_trace_log_2,
        attributes.static_smem_bytes,
        device_cap_bytes,
    );

    let mut selected: Vec<usize> = layers
        .iter()
        .map(|layer| layer.capacity.dynamic_smem_bytes)
        .collect();
    selected.sort_unstable();
    selected.dedup();
    let max_dynamic = *selected
        .last()
        .expect("a non-empty layer plan yields at least one selected size");

    let retained_ceiling = attributes.max_dynamic_smem_bytes.max(max_dynamic);
    super::kernels::set_dr_tail_max_dynamic_smem_bytes(retained_ceiling)?;
    let effective = super::kernels::dr_tail_attributes()?.max_dynamic_smem_bytes;
    assert!(max_dynamic <= effective);

    for dynamic_bytes in selected {
        assert_ne!(super::kernels::dr_tail_occupancy(dynamic_bytes)?, 0);
    }

    Ok(DrTailProofPlan {
        device_id,
        static_smem_bytes: attributes.static_smem_bytes,
        device_cap_bytes,
        layers,
        window_programs,
    })
}
