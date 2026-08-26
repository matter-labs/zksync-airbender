//! Device-resource admission for the DR-tail launcher.
//!
//! This module deliberately keeps the resource record separate from
//! `GkrPrograms`: attributes are device- and launch-configuration-specific and
//! must be queried on the scheduling thread for each proof admission.
//!
//! `maxDynamicSharedSizeBytes` is kernel-wide mutable state. Admission never
//! lowers it because an earlier proof may still be waiting to enqueue a launch
//! that needs the existing ceiling.

use std::collections::BTreeSet;

use super::capacity::{portable_entry, DrTailCapacityDecision, DrTailCapacityRequest};
use crate::backward::derive_dimension_reducing_inputs;
use crate::backward::main_layer::blueprints::build_dimension_reducing_slots_static;
use crate::storage_layout::GpuGKRStorageLayout;
use crate::upstream::{GKRAddress, GKRCircuitArtifact, PrimeField};
use era_cudart::result::CudaResult;

struct DrTailLayerInput {
    layer_idx: usize,
    folding_steps: usize,
    entry_round: usize,
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
            entry_round: portable_entry(folding_steps),
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

/// Device queries used by DR-tail resource admission.
pub(crate) trait DrTailDeviceQueries {
    fn attributes(&self) -> CudaResult<DrTailRawAttributes>;
    fn device_optin_cap_bytes(&self) -> CudaResult<usize>;
    fn set_max_dynamic_smem_bytes(&self, bytes: usize) -> CudaResult<()>;
    fn occupancy(&self, dynamic_smem_bytes: usize) -> CudaResult<u32>;
}

/// A per-proof plan. Its fields are private and the only constructor is
/// [`admit_dr_tail_resources`], so a plan handed to `prove()` cannot have
/// skipped admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrTailProofPlan {
    static_smem_bytes: usize,
    device_cap_bytes: usize,
    layers: Vec<DrTailLayerPlan>,
}

impl DrTailProofPlan {
    pub(crate) fn layers(&self) -> &[DrTailLayerPlan] {
        &self.layers
    }

    /// Recomputes the admitted plan before enqueueing any work.
    pub(crate) fn validate_before_enqueue(
        &self,
        artifact: &GKRCircuitArtifact<crate::upstream::BabyBearField>,
        final_trace_log_2: usize,
    ) {
        let expected = plan_dr_tail_layers(
            artifact,
            final_trace_log_2,
            self.static_smem_bytes,
            self.device_cap_bytes,
        );
        assert_eq!(expected.len(), self.layers.len());
        let mut seen = BTreeSet::new();
        for (expected, observed) in expected.iter().zip(&self.layers) {
            assert!(seen.insert(observed.layer_idx));
            observed.validate(DrTailLayerIdentity::new(
                expected.layer_idx,
                expected.folding_steps,
                &expected.canonical_sources,
            ));
            assert_eq!(observed.capacity, expected.capacity);
            assert_eq!(
                observed.continuation_window_count,
                expected.continuation_window_count
            );
            assert_eq!(
                observed.megakernel_entry_round,
                expected.megakernel_entry_round
            );
        }
    }
}

/// One admitted capacity bound to its artifact layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DrTailLayerPlan {
    layer_idx: usize,
    folding_steps: usize,
    canonical_sources: Vec<GKRAddress>,
    continuation_window_count: usize,
    megakernel_entry_round: usize,
    capacity: DrTailCapacityDecision,
}

/// Copyable execution portion of one identity-bound, preflight-derived layer
/// plan. Scheduling consumes this value and never recomputes its window count
/// or recursive-tail boundary from runtime state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrLayerExecutionPlan {
    continuation_window_count: usize,
    megakernel_entry_round: usize,
    capacity: DrTailCapacityDecision,
}

impl DrLayerExecutionPlan {
    pub(crate) const fn continuation_window_count(self) -> usize {
        self.continuation_window_count
    }

    pub(crate) const fn megakernel_entry_round(self) -> usize {
        self.megakernel_entry_round
    }

    pub(crate) const fn capacity(self) -> DrTailCapacityDecision {
        self.capacity
    }
}

impl DrTailLayerPlan {
    fn new(
        layer_idx: usize,
        folding_steps: usize,
        canonical_sources: Vec<GKRAddress>,
        capacity: DrTailCapacityDecision,
    ) -> Self {
        let megakernel_entry_round = capacity.entry_round();
        let continuation_window_count = megakernel_entry_round
            .checked_sub(3)
            .expect("an admitted DR tail starts after windowed R0")
            / 3;
        debug_assert_eq!(megakernel_entry_round, 3 + 3 * continuation_window_count);
        Self {
            layer_idx,
            folding_steps,
            canonical_sources,
            continuation_window_count,
            megakernel_entry_round,
            capacity,
        }
    }

    pub(crate) const fn execution_plan(&self) -> DrLayerExecutionPlan {
        DrLayerExecutionPlan {
            continuation_window_count: self.continuation_window_count,
            megakernel_entry_round: self.megakernel_entry_round,
            capacity: self.capacity,
        }
    }

    const fn dynamic_smem_bytes(&self) -> usize {
        self.capacity.dynamic_smem_bytes()
    }

    fn validate(&self, expected: DrTailLayerIdentity<'_>) {
        assert_eq!(self.layer_idx, expected.layer_idx);
        assert_eq!(self.folding_steps, expected.folding_steps);
        assert_eq!(self.canonical_sources, expected.canonical_sources);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailLayerIdentity<'a> {
    layer_idx: usize,
    folding_steps: usize,
    canonical_sources: &'a [GKRAddress],
}

impl<'a> DrTailLayerIdentity<'a> {
    pub(crate) const fn new(
        layer_idx: usize,
        folding_steps: usize,
        canonical_sources: &'a [GKRAddress],
    ) -> Self {
        Self {
            layer_idx,
            folding_steps,
            canonical_sources,
        }
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

    pub(crate) fn bind(&mut self, expected: DrTailLayerIdentity<'_>) -> DrLayerExecutionPlan {
        let planned = self
            .layers
            .iter()
            .find(|planned| planned.layer_idx == expected.layer_idx)
            .expect("DR-tail plan is missing a layer");
        planned.validate(expected);
        assert!(self.consumed.insert(expected.layer_idx));
        planned.execution_plan()
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
            let capacity = DrTailCapacityRequest {
                folding_steps: input.folding_steps,
                entry_round: input.entry_round,
                canonical_sources: canonical_sources.len(),
                static_smem_bytes,
                device_cap_bytes,
            }
            .decide();
            DrTailLayerPlan::new(
                input.layer_idx,
                input.folding_steps,
                canonical_sources,
                capacity,
            )
        })
        .collect()
}

pub(crate) fn admit_dr_tail_resources<F: PrimeField, Q: DrTailDeviceQueries>(
    queries: &Q,
    artifact: &GKRCircuitArtifact<F>,
    final_trace_log_2: usize,
) -> CudaResult<DrTailProofPlan> {
    let attributes = queries.attributes()?;
    assert_eq!(
        attributes.local_bytes, 0,
        "DR-tail kernel spills to local memory"
    );
    let device_cap_bytes = queries.device_optin_cap_bytes()?;

    let layers = plan_dr_tail_layers(
        artifact,
        final_trace_log_2,
        attributes.static_smem_bytes,
        device_cap_bytes,
    );

    let mut selected: Vec<usize> = layers
        .iter()
        .map(DrTailLayerPlan::dynamic_smem_bytes)
        .collect();
    selected.sort_unstable();
    selected.dedup();
    let max_dynamic = *selected
        .last()
        .expect("a non-empty layer plan yields at least one selected size");

    let retained_ceiling = attributes.max_dynamic_smem_bytes.max(max_dynamic);
    queries.set_max_dynamic_smem_bytes(retained_ceiling)?;
    let effective = queries.attributes()?.max_dynamic_smem_bytes;
    assert!(max_dynamic <= effective);

    for dynamic_bytes in selected {
        assert_ne!(queries.occupancy(dynamic_bytes)?, 0);
    }

    Ok(DrTailProofPlan {
        static_smem_bytes: attributes.static_smem_bytes,
        device_cap_bytes,
        layers,
    })
}
