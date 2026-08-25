//! Device-resource admission for the DR-tail launcher.
//!
//! This module deliberately keeps the resource record separate from
//! `GkrPrograms`: attributes are device- and launch-configuration-specific and
//! must be queried on the scheduling thread for each proof admission.
//!
//! Ordering matters. `maxDynamicSharedSizeBytes` reported by
//! `cudaFuncGetAttributes` is the kernel's *current* opt-in ceiling, which is
//! the architecture default until `cudaFuncSetAttribute` raises it, and CUDA
//! documents that attribute as a hint the driver may adjust. Occupancy is
//! therefore only meaningful once the ceiling has been raised to the maximum
//! selected dynamic size. [`admit_dr_tail_resources`] enforces that sequence.

use std::collections::BTreeSet;

use super::capacity::{
    DrTailCapacityDecision, DrTailCapacityRejection, DrTailCapacityRequest, DrTailEntrySelection,
};
use super::census::dr_tail_layer_inputs;
use crate::upstream::{GKRAddress, GKRCircuitArtifact, PrimeField};
use era_cudart_sys::CudaError;

/// Threads per DR-tail block; occupancy is queried at exactly this width.
pub(crate) const DR_TAIL_OCCUPANCY_THREADS: u32 = super::kernels::DR_TAIL_BLOCK_THREADS;

/// Raw linked-kernel attributes, as reported by `cudaFuncGetAttributes`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DrTailRawAttributes {
    pub static_smem_bytes: usize,
    pub local_bytes: usize,
    pub registers: i32,
    /// The kernel's current dynamic opt-in ceiling.
    pub max_dynamic_smem_bytes: usize,
}

/// Device queries the admission sequence needs. Implemented once against CUDA
/// in `kernels.rs`, and by an event-recording fake in tests so cap and
/// occupancy rejection are provable without a device.
pub(crate) trait DrTailDeviceQueries {
    fn attributes(&self) -> Result<DrTailRawAttributes, DrTailResourceError>;
    fn device_optin_cap_bytes(&self) -> Result<usize, DrTailResourceError>;
    fn set_max_dynamic_smem_bytes(&self, bytes: usize) -> Result<(), DrTailResourceError>;
    fn occupancy(&self, dynamic_smem_bytes: usize) -> Result<u32, DrTailResourceError>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrTailKernelResources {
    static_smem_bytes: usize,
    local_bytes: usize,
    registers: i32,
    device_optin_cap_bytes: usize,
    effective_max_dynamic_smem_bytes: usize,
    occupancy_by_dynamic_bytes: Vec<(usize, u32)>,
}

impl DrTailKernelResources {
    pub const fn static_smem_bytes(&self) -> usize {
        self.static_smem_bytes
    }

    pub const fn local_bytes(&self) -> usize {
        self.local_bytes
    }

    pub const fn registers(&self) -> i32 {
        self.registers
    }

    pub const fn effective_max_dynamic_smem_bytes(&self) -> usize {
        self.effective_max_dynamic_smem_bytes
    }

    pub(crate) const fn device_optin_cap_bytes(&self) -> usize {
        self.device_optin_cap_bytes
    }

    pub fn occupancy_by_dynamic_bytes(&self) -> &[(usize, u32)] {
        &self.occupancy_by_dynamic_bytes
    }
}

/// A per-proof plan. Its fields are private and the only constructor is
/// [`admit_dr_tail_resources`], so a plan handed to `prove()` cannot have
/// skipped admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrTailProofPlan {
    resources: DrTailKernelResources,
    layers: Vec<DrTailLayerPlan>,
    /// The entry selection this plan was admitted under. Pre-enqueue
    /// validation recomputes the census with exactly this value, so a plan
    /// admitted for a diagnostic entry can never be re-validated as portable.
    entry: DrTailEntrySelection,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DrTailScheduleError {
    Cuda(CudaError),
    Identity(DrTailPlanIdentityError),
    DuplicateEqOwner {
        observed: usize,
    },
    FinalPublicationStrideMismatch {
        owner_log2_stride: u32,
        planned_log2_stride: u32,
        planned_per_poly_len: usize,
        selected_log2_stride: u32,
    },
    WindowBinding {
        detail: String,
    },
    MissingCompleteChainContract,
}

impl From<CudaError> for DrTailScheduleError {
    fn from(error: CudaError) -> Self {
        Self::Cuda(error)
    }
}

impl From<DrTailPlanIdentityError> for DrTailScheduleError {
    fn from(error: DrTailPlanIdentityError) -> Self {
        Self::Identity(error)
    }
}

impl core::fmt::Display for DrTailScheduleError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DrTailScheduleError {}

impl DrTailProofPlan {
    pub fn resources(&self) -> &DrTailKernelResources {
        &self.resources
    }

    pub fn layers(&self) -> &[DrTailLayerPlan] {
        &self.layers
    }

    pub const fn entry(&self) -> DrTailEntrySelection {
        self.entry
    }

    /// Complete host-side identity of the resource plan admitted for one
    /// measured proof. This records decisions already made by preflight; it
    /// performs no device query and schedules no work.
    #[doc(hidden)]
    pub fn exact_memory_identity_json(&self, device_id: i32) -> serde_json::Value {
        serde_json::json!({
            "device_id": device_id,
            "admitted": true,
            "entry": self.entry.label(),
            "kernel": {
                "static_smem_bytes": self.resources.static_smem_bytes,
                "local_bytes": self.resources.local_bytes,
                "registers": self.resources.registers,
                "device_optin_cap_bytes": self.resources.device_optin_cap_bytes,
                "effective_max_dynamic_smem_bytes": self.resources.effective_max_dynamic_smem_bytes,
                "occupancy_by_dynamic_bytes": self.resources.occupancy_by_dynamic_bytes,
            },
            "layers": self.layers.iter().map(|layer| serde_json::json!({
                "layer_idx": layer.layer_idx,
                "folding_steps": layer.folding_steps,
                "canonical_sources": layer.canonical_sources.iter()
                    .map(|address| format!("{address:?}"))
                    .collect::<Vec<_>>(),
                "entry_round": layer.capacity.entry_round,
                "remaining_rounds": layer.capacity.remaining_rounds,
                "entry_cells_per_source": layer.capacity.entry_cells_per_source,
                "state_bytes": layer.capacity.state_bytes,
                "eq_suffix_offset": layer.capacity.eq_suffix_offset,
                "eq_suffix_bits": layer.capacity.eq_suffix_bits,
                "eq_group_count": layer.capacity.eq_group_count,
                "factored_eq_bytes": layer.capacity.factored_eq_bytes,
                "dynamic_smem_bytes": layer.capacity.dynamic_smem_bytes,
                "static_smem_bytes": layer.capacity.static_smem_bytes,
                "total_smem_bytes": layer.capacity.total_smem_bytes,
            })).collect::<Vec<_>>(),
        })
    }

    /// Validate the complete admitted identity before the scheduler can enqueue
    /// any work.  Recomputing the census here also binds capacities, not just
    /// the layer labels, so swapped or stale decisions cannot launch.
    pub(crate) fn validate_before_enqueue(
        &self,
        artifact: &GKRCircuitArtifact<crate::upstream::BabyBearField>,
        final_trace_log_2: usize,
    ) -> Result<(), DrTailPlanIdentityError> {
        let expected = plan_dr_tail_layers(
            artifact,
            final_trace_log_2,
            self.resources.static_smem_bytes,
            self.resources.device_optin_cap_bytes,
            self.entry,
        )
        .map_err(|error| DrTailPlanIdentityError::CapacityDerivation {
            detail: format!("{error:?}"),
        })?;
        if expected.len() != self.layers.len() {
            return Err(DrTailPlanIdentityError::CountMismatch {
                expected: expected.len(),
                observed: self.layers.len(),
            });
        }
        let mut seen = BTreeSet::new();
        for (expected, observed) in expected.iter().zip(&self.layers) {
            if !seen.insert(observed.layer_idx) {
                return Err(DrTailPlanIdentityError::DuplicateLayer {
                    layer_idx: observed.layer_idx,
                });
            }
            observed.validate(DrTailLayerIdentity::new(
                expected.layer_idx,
                expected.folding_steps,
                &expected.canonical_sources,
            ))?;
            if observed.capacity != expected.capacity {
                return Err(DrTailPlanIdentityError::CapacityMismatch {
                    layer_idx: expected.layer_idx,
                });
            }
            if observed.continuation_window_count != expected.continuation_window_count {
                return Err(DrTailPlanIdentityError::ContinuationWindowCountMismatch {
                    layer_idx: expected.layer_idx,
                    expected: expected.continuation_window_count,
                    observed: observed.continuation_window_count,
                });
            }
            if observed.megakernel_entry_round != expected.megakernel_entry_round {
                return Err(DrTailPlanIdentityError::MegakernelEntryRoundMismatch {
                    layer_idx: expected.layer_idx,
                    expected: expected.megakernel_entry_round,
                    observed: observed.megakernel_entry_round,
                });
            }
        }
        Ok(())
    }
}

/// One admitted capacity bound to the exact artifact-layer identity that
/// produced it. The absolute layer key is retained because production walks
/// the DR tower in reverse while the census emits it in ascending order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrTailLayerPlan {
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

    pub(crate) const fn entry_round(self) -> usize {
        self.megakernel_entry_round
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

    pub const fn layer_idx(&self) -> usize {
        self.layer_idx
    }

    pub const fn folding_steps(&self) -> usize {
        self.folding_steps
    }

    pub fn canonical_source_count(&self) -> usize {
        self.canonical_sources.len()
    }

    pub(crate) fn canonical_sources(&self) -> &[GKRAddress] {
        &self.canonical_sources
    }

    pub const fn capacity(&self) -> &DrTailCapacityDecision {
        &self.capacity
    }

    pub(crate) const fn execution_plan(&self) -> DrLayerExecutionPlan {
        DrLayerExecutionPlan {
            continuation_window_count: self.continuation_window_count,
            megakernel_entry_round: self.megakernel_entry_round,
            capacity: self.capacity,
        }
    }

    pub const fn dynamic_smem_bytes(&self) -> usize {
        self.capacity.dynamic_smem_bytes()
    }

    fn validate(&self, expected: DrTailLayerIdentity<'_>) -> Result<(), DrTailPlanIdentityError> {
        if self.layer_idx != expected.layer_idx {
            return Err(DrTailPlanIdentityError::LayerMismatch {
                expected: expected.layer_idx,
                observed: self.layer_idx,
            });
        }
        if self.folding_steps != expected.folding_steps {
            return Err(DrTailPlanIdentityError::FoldingStepsMismatch {
                layer_idx: expected.layer_idx,
                expected: expected.folding_steps,
                observed: self.folding_steps,
            });
        }
        if self.canonical_sources != expected.canonical_sources {
            return Err(DrTailPlanIdentityError::CanonicalSourcesMismatch {
                layer_idx: expected.layer_idx,
                expected: expected.canonical_sources.to_vec(),
                observed: self.canonical_sources.clone(),
            });
        }
        Ok(())
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DrTailPlanIdentityError {
    CountMismatch {
        expected: usize,
        observed: usize,
    },
    CapacityDerivation {
        detail: String,
    },
    CapacityMismatch {
        layer_idx: usize,
    },
    ContinuationWindowCountMismatch {
        layer_idx: usize,
        expected: usize,
        observed: usize,
    },
    MegakernelEntryRoundMismatch {
        layer_idx: usize,
        expected: usize,
        observed: usize,
    },
    MissingLayer {
        layer_idx: usize,
    },
    DuplicateLayer {
        layer_idx: usize,
    },
    LayerMismatch {
        expected: usize,
        observed: usize,
    },
    FoldingStepsMismatch {
        layer_idx: usize,
        expected: usize,
        observed: usize,
    },
    CanonicalSourcesMismatch {
        layer_idx: usize,
        expected: Vec<GKRAddress>,
        observed: Vec<GKRAddress>,
    },
    UnconsumedLayers {
        planned: usize,
        consumed: usize,
    },
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
        expected: DrTailLayerIdentity<'_>,
    ) -> Result<DrLayerExecutionPlan, DrTailPlanIdentityError> {
        let planned = self
            .layers
            .iter()
            .find(|planned| planned.layer_idx == expected.layer_idx)
            .ok_or(DrTailPlanIdentityError::MissingLayer {
                layer_idx: expected.layer_idx,
            })?;
        planned.validate(expected)?;
        if !self.consumed.insert(expected.layer_idx) {
            return Err(DrTailPlanIdentityError::DuplicateLayer {
                layer_idx: expected.layer_idx,
            });
        }
        Ok(planned.execution_plan())
    }

    pub(crate) fn finish(self) -> Result<(), DrTailPlanIdentityError> {
        if self.consumed.len() != self.layers.len() {
            return Err(DrTailPlanIdentityError::UnconsumedLayers {
                planned: self.layers.len(),
                consumed: self.consumed.len(),
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DrTailResourceError {
    /// The linked kernel spills to local memory.
    LocalMemorySpill { bytes: usize },
    /// The opt-in ceiling did not reach the largest selected request.
    DynamicMemoryExceedsOptIn { required: usize, cap: usize },
    /// No block can be resident at the selected size.
    ZeroOccupancy { dynamic_bytes: usize },
    /// A production proof selected no DR layer.
    MissingLayerPlan,
    /// The pure capacity pass rejected a production layer. A layer whose
    /// static plus dynamic shared memory exceeds the device per-block cap is
    /// rejected here, as
    /// [`DrTailCapacityRejection::DeviceCapacityExceeded`].
    Capacity {
        layer_idx: usize,
        rejection: DrTailCapacityRejection,
    },
    /// A CUDA query failed.
    Cuda { call: &'static str, code: i32 },
}

impl std::fmt::Display for DrTailResourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for DrTailResourceError {}

/// Resolve every production DR layer to a capacity decision.
///
/// CPU-only: the measured static shared bytes and the device per-block cap are
/// supplied by the caller, so this is exercisable without a device.
pub(crate) fn plan_dr_tail_layers<F: PrimeField>(
    artifact: &GKRCircuitArtifact<F>,
    final_trace_log_2: usize,
    static_smem_bytes: usize,
    device_cap_bytes: usize,
    entry: DrTailEntrySelection,
) -> Result<Vec<DrTailLayerPlan>, DrTailResourceError> {
    let inputs = dr_tail_layer_inputs(artifact, final_trace_log_2, entry).map_err(|rejection| {
        DrTailResourceError::Capacity {
            layer_idx: usize::MAX,
            rejection,
        }
    })?;
    if inputs.is_empty() {
        return Err(DrTailResourceError::MissingLayerPlan);
    }
    inputs
        .into_iter()
        .map(|input| {
            let canonical_sources = input.order.sorted_canonical;
            assert_eq!(canonical_sources.len(), input.canonical_sources);
            let capacity = DrTailCapacityRequest {
                folding_steps: input.folding_steps,
                entry_round: input.entry_round,
                canonical_sources: canonical_sources.len(),
                static_smem_bytes,
                device_cap_bytes,
            }
            .decide()
            .map_err(|rejection| DrTailResourceError::Capacity {
                layer_idx: input.layer_idx,
                rejection,
            })?;
            Ok(DrTailLayerPlan::new(
                input.layer_idx,
                input.folding_steps,
                canonical_sources,
                capacity,
            ))
        })
        .collect()
}

/// The admission sequence, in the order the device requires.
///
/// 1. read static/local/register attributes;
/// 2. plan every production layer against the measured static bytes and the
///    device per-block cap (a layer over the cap is rejected here, as
///    `Capacity { DeviceCapacityExceeded }`);
/// 3. raise the dynamic opt-in ceiling exactly once, to the largest selected
///    size;
/// 4. re-read the attributes so the *effective* ceiling is what is checked;
/// 5. query occupancy per distinct selected size;
/// 6. admit.
pub(crate) fn admit_dr_tail_resources<F: PrimeField, Q: DrTailDeviceQueries>(
    queries: &Q,
    artifact: &GKRCircuitArtifact<F>,
    final_trace_log_2: usize,
    entry: DrTailEntrySelection,
) -> Result<DrTailProofPlan, DrTailResourceError> {
    let attributes = queries.attributes()?;
    if attributes.local_bytes != 0 {
        return Err(DrTailResourceError::LocalMemorySpill {
            bytes: attributes.local_bytes,
        });
    }
    let device_cap_bytes = queries.device_optin_cap_bytes()?;

    let layers = plan_dr_tail_layers(
        artifact,
        final_trace_log_2,
        attributes.static_smem_bytes,
        device_cap_bytes,
        entry,
    )?;
    if layers.is_empty() {
        return Err(DrTailResourceError::MissingLayerPlan);
    }

    let mut selected: Vec<usize> = layers
        .iter()
        .map(DrTailLayerPlan::dynamic_smem_bytes)
        .collect();
    selected.sort_unstable();
    selected.dedup();
    let max_dynamic = *selected
        .last()
        .expect("a non-empty layer plan yields at least one selected size");

    queries.set_max_dynamic_smem_bytes(max_dynamic)?;
    let effective = queries.attributes()?.max_dynamic_smem_bytes;
    if max_dynamic > effective {
        return Err(DrTailResourceError::DynamicMemoryExceedsOptIn {
            required: max_dynamic,
            cap: effective,
        });
    }

    let mut occupancy_by_dynamic_bytes = Vec::with_capacity(selected.len());
    for dynamic_bytes in selected {
        let occupancy = queries.occupancy(dynamic_bytes)?;
        if occupancy == 0 {
            return Err(DrTailResourceError::ZeroOccupancy { dynamic_bytes });
        }
        occupancy_by_dynamic_bytes.push((dynamic_bytes, occupancy));
    }

    Ok(DrTailProofPlan {
        resources: DrTailKernelResources {
            static_smem_bytes: attributes.static_smem_bytes,
            local_bytes: attributes.local_bytes,
            registers: attributes.registers,
            device_optin_cap_bytes: device_cap_bytes,
            effective_max_dynamic_smem_bytes: effective,
            occupancy_by_dynamic_bytes,
        },
        layers,
        entry,
    })
}

/// A synthetic, CPU-only device for this module's admission tests. Private
/// and test-gated: no production-visible path can mint a plan from it.
#[cfg(test)]
mod fake {
    use super::*;
    use std::cell::RefCell;

    /// One recorded device interaction, in call order.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum FakeDeviceEvent {
        Attributes,
        DeviceOptInCap,
        SetMaxDynamicSmemBytes(usize),
        Occupancy(usize),
    }

    /// Event-recording fake. The recorded sequence proves the exact query
    /// and setter ordering and counts; the tunable fields drive the cap and
    /// occupancy rejections.
    pub struct FakeQueries {
        pub attributes: RefCell<DrTailRawAttributes>,
        pub device_cap_bytes: usize,
        pub occupancy: u32,
        pub grant_optin: bool,
        pub events: RefCell<Vec<FakeDeviceEvent>>,
    }

    impl FakeQueries {
        pub fn healthy(device_cap_bytes: usize) -> Self {
            Self {
                attributes: RefCell::new(DrTailRawAttributes {
                    static_smem_bytes: 0,
                    local_bytes: 0,
                    registers: 32,
                    max_dynamic_smem_bytes: 48 * 1024,
                }),
                device_cap_bytes,
                occupancy: 2,
                grant_optin: true,
                events: RefCell::new(Vec::new()),
            }
        }

        pub fn recorded(&self) -> Vec<FakeDeviceEvent> {
            self.events.borrow().clone()
        }

        fn record(&self, event: FakeDeviceEvent) {
            self.events.borrow_mut().push(event);
        }
    }

    impl DrTailDeviceQueries for FakeQueries {
        fn attributes(&self) -> Result<DrTailRawAttributes, DrTailResourceError> {
            self.record(FakeDeviceEvent::Attributes);
            Ok(*self.attributes.borrow())
        }

        fn device_optin_cap_bytes(&self) -> Result<usize, DrTailResourceError> {
            self.record(FakeDeviceEvent::DeviceOptInCap);
            Ok(self.device_cap_bytes)
        }

        /// Models the driver: a granted request never lowers the current
        /// ceiling and never exceeds the device opt-in cap. A refused request
        /// leaves the ceiling untouched, which is the case admission must
        /// reject rather than measure occupancy against.
        fn set_max_dynamic_smem_bytes(&self, bytes: usize) -> Result<(), DrTailResourceError> {
            self.record(FakeDeviceEvent::SetMaxDynamicSmemBytes(bytes));
            if self.grant_optin {
                let mut attributes = self.attributes.borrow_mut();
                attributes.max_dynamic_smem_bytes = bytes
                    .max(attributes.max_dynamic_smem_bytes)
                    .min(self.device_cap_bytes);
            }
            Ok(())
        }

        fn occupancy(&self, dynamic_smem_bytes: usize) -> Result<u32, DrTailResourceError> {
            self.record(FakeDeviceEvent::Occupancy(dynamic_smem_bytes));
            Ok(self.occupancy)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::fake::{FakeDeviceEvent, FakeQueries};
    use super::*;
    use crate::backward::dim_reducing_sumcheck_plan::{
        schedule_dr_layer_execution, DrLayerExecutionContract, DrLayerExecutionSelection,
        DrLayerExecutionStage,
    };
    use crate::backward::{compile_corpus_layout, CONTINUATION_GOLDEN_CORPUS};

    const FINAL_TRACE_LOG: usize = 4;
    const DEVICE_CAP: usize = 101_376;

    fn artifact() -> std::sync::Arc<GKRCircuitArtifact<gpu_core::primitives::field::BF>> {
        let (programs, _) = compile_corpus_layout("blake2_with_extended_control_layout_gkr.json");
        programs.runtime_circuit().clone()
    }

    /// Bound disposition of every diagnostic neighbour across the committed
    /// corpus. The packet's entry sweep needs a host-side expectation for each
    /// neighbour instead of discovering it on the device, so this records which
    /// entries are legal and capacity-passing and which are typed rejections.
    #[test]
    fn cpu_dr_tail_entry_sweep_disposition_is_bound_for_the_corpus() {
        let mut lines = Vec::new();
        for (layout_name, _) in CONTINUATION_GOLDEN_CORPUS {
            let layout_name: &'static str = layout_name;
            let (programs, _) = compile_corpus_layout(layout_name);
            let artifact = programs.runtime_circuit();
            for selection in [
                DrTailEntrySelection::Portable,
                DrTailEntrySelection::Minus3,
                DrTailEntrySelection::Plus3,
            ] {
                let outcome = plan_dr_tail_layers(
                    artifact.as_ref(),
                    FINAL_TRACE_LOG,
                    0,
                    DEVICE_CAP,
                    selection,
                );
                let summary = match &outcome {
                    Ok(layers) => format!(
                        "admits entries={:?}",
                        layers
                            .iter()
                            .map(|layer| layer.capacity.entry_round())
                            .collect::<Vec<_>>()
                    ),
                    Err(error) => format!("rejects {error:?}"),
                };
                lines.push(format!("{layout_name} {} {summary}", selection.label()));
            }
        }
        for line in &lines {
            eprintln!("{line}");
        }
        // Portable admits every layout; that is the production path.
        assert!(
            lines
                .iter()
                .filter(|line| line.contains(" portable "))
                .all(|line| line.contains("admits")),
            "the portable entry must admit every committed layout"
        );
        // Bound disposition: at this geometry no adjacent neighbour is legal
        // and capacity-passing, so the set of capacity-passing neighbours is
        // empty and every neighbour is a typed pre-enqueue rejection.
        // `portable_entry` already selects the largest legal width-three
        // boundary, so `plus3` runs past the final round; `minus3` raises
        // `entry_cells_per_source` by 2^3 and exceeds the device cap.
        for line in lines.iter().filter(|line| line.contains(" plus3 ")) {
            assert!(
                line.contains("rejects Capacity") && line.contains("EntryAtOrAfterFinalRound"),
                "plus3 must be a typed after-final-round rejection: {line}"
            );
        }
        for line in lines.iter().filter(|line| line.contains(" minus3 ")) {
            assert!(
                line.contains("rejects Capacity")
                    && (line.contains("DeviceCapacityExceeded")
                        || line.contains("EntryBeforeFirstWindow")),
                "minus3 must be a typed capacity or first-window rejection: {line}"
            );
        }
        assert_eq!(
            lines.len(),
            CONTINUATION_GOLDEN_CORPUS.len() * 3,
            "every layout must report a disposition for all three entries"
        );
    }

    /// B6: the diagnostic entry override runs through the very same capacity
    /// decision as production. The portable entry is unchanged, each legal
    /// neighbour shifts every layer by exactly one width-three boundary, and an
    /// illegal or capacity-failing neighbour is a typed rejection produced
    /// before any plan exists — so nothing can be enqueued.
    #[test]
    fn cpu_dr_tail_entry_override_decides_through_production_capacity() {
        let artifact = artifact();
        let portable = plan_dr_tail_layers(
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            0,
            DEVICE_CAP,
            DrTailEntrySelection::Portable,
        )
        .expect("the portable entry admits");

        // Production default is untouched by the existence of the override.
        let default_entry = DrTailEntrySelection::default();
        assert_eq!(default_entry, DrTailEntrySelection::Portable);
        assert_eq!(default_entry.label(), "portable");
        assert_eq!(
            DrTailEntrySelection::from_label("portable"),
            Some(DrTailEntrySelection::Portable)
        );
        assert_eq!(DrTailEntrySelection::from_label("r+3"), None);

        for (selection, delta) in [
            (DrTailEntrySelection::Minus3, -3i64),
            (DrTailEntrySelection::Plus3, 3),
        ] {
            let shifted =
                plan_dr_tail_layers(artifact.as_ref(), FINAL_TRACE_LOG, 0, DEVICE_CAP, selection);
            let Ok(shifted) = shifted else {
                // A neighbour that no layer can legally take is refused by the
                // production capacity pass, which is the accepted behaviour.
                let error = shifted.expect_err("checked above");
                assert!(
                    matches!(error, DrTailResourceError::Capacity { .. }),
                    "a rejected neighbour must be a typed capacity rejection: {error:?}"
                );
                continue;
            };
            assert_eq!(shifted.len(), portable.len(), "{selection:?}");
            for (base, moved) in portable.iter().zip(&shifted) {
                assert_eq!(moved.layer_idx, base.layer_idx);
                assert_eq!(
                    i64::try_from(moved.capacity.entry_round()).unwrap(),
                    i64::try_from(base.capacity.entry_round()).unwrap() + delta,
                    "{selection:?} must move every entry by exactly one boundary"
                );
                // Every shifted decision still came from `decide`, so it keeps
                // the width-three boundary and stays inside the device cap.
                assert_eq!(moved.capacity.entry_round() % 3, 0);
                assert!(moved.capacity.total_smem_bytes() <= DEVICE_CAP);
            }
        }

        // An admitted plan records its own entry, so pre-enqueue validation
        // recomputes with it and a portable plan can never be revalidated as a
        // neighbour's.
        let queries = FakeQueries::healthy(DEVICE_CAP);
        let plan = admit_dr_tail_resources(
            &queries,
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect("portable admission");
        assert_eq!(plan.entry(), DrTailEntrySelection::Portable);
        assert_eq!(
            plan.validate_before_enqueue(artifact.as_ref(), FINAL_TRACE_LOG),
            Ok(())
        );
        let mut swapped = plan.clone();
        swapped.entry = DrTailEntrySelection::Plus3;
        let revalidated = swapped.validate_before_enqueue(artifact.as_ref(), FINAL_TRACE_LOG);
        assert_ne!(
            revalidated,
            Ok(()),
            "a plan whose entry was swapped must not revalidate"
        );

        // A neighbour whose entry cannot exist is refused before admission
        // returns, so no plan and therefore no enqueue is possible.
        let starved = FakeQueries::healthy(1);
        assert!(matches!(
            admit_dr_tail_resources(
                &starved,
                artifact.as_ref(),
                FINAL_TRACE_LOG,
                DrTailEntrySelection::Plus3,
            ),
            Err(DrTailResourceError::Capacity { .. })
        ));
    }

    /// Test 1 of the advisory: production layer coverage, shared with the
    /// census. Every DR layer of the tower yields exactly one decision.
    #[test]
    fn cpu_dr_tail_resource_layer_coverage() {
        let artifact = artifact();
        let inputs = super::super::census::dr_tail_layer_inputs(
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect("production tower must resolve");
        let layers = plan_dr_tail_layers(
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            0,
            DEVICE_CAP,
            DrTailEntrySelection::Portable,
        )
        .expect("production layers must be admissible");
        assert_eq!(
            layers.len(),
            inputs.len(),
            "one decision per production DR layer"
        );
        assert!(!layers.is_empty(), "the corpus layout has DR layers");
        for (decision, input) in layers.iter().zip(inputs.iter()) {
            assert_eq!(decision.layer_idx(), input.layer_idx);
            assert_eq!(decision.folding_steps(), input.folding_steps);
            assert_eq!(
                decision.canonical_sources(),
                input.order.sorted_canonical.as_slice()
            );
            assert_eq!(decision.capacity().entry_round(), input.entry_round);
        }
    }

    #[test]
    fn cpu_dr_layer_execution_plan_is_preflight_derived_and_mutation_sensitive() {
        let artifact = artifact();
        let layers = plan_dr_tail_layers(
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            0,
            DEVICE_CAP,
            DrTailEntrySelection::Portable,
        )
        .expect("production layers must be admissible");

        for layer in &layers {
            let execution = layer.execution_plan();
            assert_eq!(
                execution.megakernel_entry_round(),
                layer.capacity().entry_round(),
                "resource capacity and the execution boundary must be one plan",
            );
            assert_eq!(
                execution.continuation_window_count(),
                (execution.megakernel_entry_round() - 3) / 3,
                "preflight must derive every width-three continuation",
            );
            let contract = DrLayerExecutionContract::minimal_valid_for_test();
            let mut observed = Vec::new();
            schedule_dr_layer_execution(
                Some(&contract),
                DrLayerExecutionSelection::CompleteNewChain {
                    continuation_count: execution.continuation_window_count(),
                },
                Some(&mut |stage| observed.push(stage)),
                |_| Ok::<(), DrTailScheduleError>(()),
            )
            .expect("the admitted execution plan must enumerate the complete chain");
            assert_eq!(observed.first(), Some(&DrLayerExecutionStage::R0));
            assert_eq!(observed.last(), Some(&DrLayerExecutionStage::Megakernel));
            assert_eq!(
                observed.len(),
                execution.continuation_window_count() + 2,
                "R0 and the recursive tail must bracket every planned continuation",
            );
        }

        let mut plan = admit_dr_tail_resources(
            &FakeQueries::healthy(DEVICE_CAP),
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect("production fixture must admit");
        plan.layers[0].continuation_window_count -= 1;
        assert!(matches!(
            plan.validate_before_enqueue(artifact.as_ref(), FINAL_TRACE_LOG),
            Err(DrTailPlanIdentityError::ContinuationWindowCountMismatch { .. })
        ));
    }

    #[test]
    fn cpu_plan_identity_mutations_reject_before_any_launch() {
        fn admitted() -> (
            std::sync::Arc<GKRCircuitArtifact<gpu_core::primitives::field::BF>>,
            DrTailProofPlan,
        ) {
            let artifact = artifact();
            let queries = FakeQueries::healthy(DEVICE_CAP);
            let plan = admit_dr_tail_resources(
                &queries,
                artifact.as_ref(),
                FINAL_TRACE_LOG,
                DrTailEntrySelection::Portable,
            )
            .expect("production fixture must admit");
            (artifact, plan)
        }
        fn rejected(
            mutate: impl FnOnce(&mut DrTailProofPlan),
            expected: impl FnOnce(&DrTailPlanIdentityError) -> bool,
        ) {
            let (artifact, mut plan) = admitted();
            mutate(&mut plan);
            let contract = DrLayerExecutionContract::minimal_valid_for_test();
            let mut observed = Vec::new();
            let mut launched = Vec::new();
            let mut observer = |stage| observed.push(stage);
            let result = plan
                .validate_before_enqueue(artifact.as_ref(), FINAL_TRACE_LOG)
                .map_err(DrTailScheduleError::from)
                .and_then(|()| {
                    schedule_dr_layer_execution(
                        Some(&contract),
                        DrLayerExecutionSelection::CompleteNewChain {
                            continuation_count: 0,
                        },
                        Some(&mut observer),
                        |stage| {
                            launched.push(stage);
                            Ok(())
                        },
                    )
                });
            let Err(DrTailScheduleError::Identity(error)) = result else {
                panic!("mutation must return its typed identity error: {result:?}");
            };
            assert!(expected(&error), "unexpected identity error: {error:?}");
            assert!(
                observed.is_empty(),
                "preflight rejection reached enqueue spy"
            );
            assert!(launched.is_empty(), "preflight rejection reached launcher");
        }

        rejected(
            |plan| {
                plan.layers.pop();
            },
            |error| matches!(error, DrTailPlanIdentityError::CountMismatch { .. }),
        );
        rejected(
            |plan| {
                let layer = plan.layers[0].clone();
                plan.layers.push(layer);
            },
            |error| matches!(error, DrTailPlanIdentityError::CountMismatch { .. }),
        );
        rejected(
            |plan| {
                plan.layers[1].layer_idx = plan.layers[0].layer_idx;
            },
            |error| matches!(error, DrTailPlanIdentityError::DuplicateLayer { .. }),
        );
        rejected(
            |plan| plan.layers.reverse(),
            |error| matches!(error, DrTailPlanIdentityError::LayerMismatch { .. }),
        );
        rejected(
            |plan| {
                let (first, rest) = plan.layers.split_at_mut(1);
                std::mem::swap(&mut first[0].capacity, &mut rest[0].capacity);
            },
            |error| matches!(error, DrTailPlanIdentityError::CapacityMismatch { .. }),
        );
        rejected(
            |plan| plan.layers[0].continuation_window_count -= 1,
            |error| {
                matches!(
                    error,
                    DrTailPlanIdentityError::ContinuationWindowCountMismatch { .. }
                )
            },
        );
        rejected(
            |plan| plan.layers[0].megakernel_entry_round -= 3,
            |error| {
                matches!(
                    error,
                    DrTailPlanIdentityError::MegakernelEntryRoundMismatch { .. }
                )
            },
        );
        rejected(
            |plan| {
                plan.layers[0].folding_steps += 1;
            },
            |error| matches!(error, DrTailPlanIdentityError::FoldingStepsMismatch { .. }),
        );
        rejected(
            |plan| {
                plan.layers[0].canonical_sources[0] = GKRAddress::ScratchSpace(usize::MAX);
            },
            |error| {
                matches!(
                    error,
                    DrTailPlanIdentityError::CanonicalSourcesMismatch { .. }
                )
            },
        );

        let (artifact, plan) = admitted();
        plan.validate_before_enqueue(artifact.as_ref(), FINAL_TRACE_LOG)
            .unwrap();
        let contract = DrLayerExecutionContract::minimal_valid_for_test();
        let mut observed = Vec::new();
        let mut launched = Vec::new();
        let mut observer = |stage| observed.push(stage);
        schedule_dr_layer_execution(
            Some(&contract),
            DrLayerExecutionSelection::CompleteNewChain {
                continuation_count: 0,
            },
            Some(&mut observer),
            |stage| {
                launched.push(stage);
                Ok::<(), DrTailScheduleError>(())
            },
        )
        .unwrap();
        assert_eq!(
            observed,
            [DrLayerExecutionStage::R0, DrLayerExecutionStage::Megakernel]
        );
        assert_eq!(launched, observed);
    }

    #[test]
    fn cpu_dr_tail_plan_binds_reversed_execution_by_absolute_identity() {
        fn layer(
            layer_idx: usize,
            folding_steps: usize,
            canonical_sources: Vec<GKRAddress>,
        ) -> DrTailLayerPlan {
            let capacity = DrTailCapacityRequest {
                folding_steps,
                entry_round: super::super::capacity::portable_entry(folding_steps).unwrap(),
                canonical_sources: canonical_sources.len(),
                static_smem_bytes: 0,
                device_cap_bytes: DEVICE_CAP,
            }
            .decide()
            .unwrap();
            DrTailLayerPlan::new(layer_idx, folding_steps, canonical_sources, capacity)
        }

        let low_sources = vec![GKRAddress::ScratchSpace(1), GKRAddress::ScratchSpace(2)];
        let high_sources = (10..17).map(GKRAddress::ScratchSpace).collect::<Vec<_>>();
        let ascending = vec![
            layer(11, 10, low_sources.clone()),
            layer(29, 20, high_sources.clone()),
        ];
        let high = DrTailLayerIdentity::new(29, 20, &high_sources);
        let low = DrTailLayerIdentity::new(11, 10, &low_sources);
        let mut cursor = DrTailPlanCursor::new(&ascending);
        assert_eq!(cursor.bind(high).unwrap().entry_round(), 15);
        assert_eq!(cursor.bind(low).unwrap().entry_round(), 9);
        assert_eq!(cursor.finish(), Ok(()));

        assert_eq!(
            ascending[0].validate(high),
            Err(DrTailPlanIdentityError::LayerMismatch {
                expected: 29,
                observed: 11,
            }),
            "the rejected ordinal lookup binds the low-fold plan to the high-fold layer",
        );

        let reversed_capacities = vec![
            DrTailLayerPlan::new(11, 20, high_sources.clone(), *ascending[1].capacity()),
            DrTailLayerPlan::new(29, 10, low_sources.clone(), *ascending[0].capacity()),
        ];
        let mut reversed = DrTailPlanCursor::new(&reversed_capacities);
        assert_eq!(
            reversed.bind(low),
            Err(DrTailPlanIdentityError::FoldingStepsMismatch {
                layer_idx: 11,
                expected: 10,
                observed: 20,
            }),
            "reversing the admitted capacities must fail before activation",
        );

        let mut duplicate = DrTailPlanCursor::new(&ascending);
        duplicate.bind(low).unwrap();
        assert_eq!(
            duplicate.bind(low),
            Err(DrTailPlanIdentityError::DuplicateLayer { layer_idx: 11 }),
        );

        let mut wrong_sources = DrTailPlanCursor::new(&ascending);
        let wrong_source_identity = vec![GKRAddress::ScratchSpace(1), GKRAddress::ScratchSpace(99)];
        assert_eq!(
            wrong_sources.bind(DrTailLayerIdentity::new(11, 10, &wrong_source_identity)),
            Err(DrTailPlanIdentityError::CanonicalSourcesMismatch {
                layer_idx: 11,
                expected: wrong_source_identity,
                observed: low_sources,
            }),
        );
    }

    /// Test 2: fake-cap rejection. One byte below the largest selected layer
    /// must reject with the exact per-layer device-capacity error, before the
    /// setter and every occupancy query; a cap of exactly that size admits.
    #[test]
    fn cpu_dr_tail_resource_cap_rejection() {
        let artifact = artifact();
        let inputs = super::super::census::dr_tail_layer_inputs(
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect("production tower must resolve");
        let layers = plan_dr_tail_layers(
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            0,
            DEVICE_CAP,
            DrTailEntrySelection::Portable,
        )
        .expect("baseline plan");
        let largest = layers
            .iter()
            .map(DrTailLayerPlan::dynamic_smem_bytes)
            .max()
            .expect("non-empty");
        // The first planned layer at the largest size is the one the
        // short-circuiting capacity pass rejects.
        let rejecting_layer_idx = inputs
            .iter()
            .zip(layers.iter())
            .find(|(_, decision)| decision.dynamic_smem_bytes() == largest)
            .map(|(input, _)| input.layer_idx)
            .expect("some layer selects the largest size");

        let healthy = FakeQueries::healthy(DEVICE_CAP);
        assert!(
            admit_dr_tail_resources(
                &healthy,
                artifact.as_ref(),
                FINAL_TRACE_LOG,
                DrTailEntrySelection::Portable
            )
            .is_ok(),
            "the unmutated device cap admits the production plan"
        );
        let exact = FakeQueries::healthy(largest);
        assert!(
            admit_dr_tail_resources(
                &exact,
                artifact.as_ref(),
                FINAL_TRACE_LOG,
                DrTailEntrySelection::Portable
            )
            .is_ok(),
            "a cap of exactly the largest total admits"
        );

        let starved = FakeQueries::healthy(largest - 1);
        let error = admit_dr_tail_resources(
            &starved,
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect_err("one byte below the largest layer must reject");
        assert_eq!(
            error,
            DrTailResourceError::Capacity {
                layer_idx: rejecting_layer_idx,
                rejection: DrTailCapacityRejection::DeviceCapacityExceeded {
                    required_bytes: largest,
                    cap_bytes: largest - 1,
                },
            },
            "cap rejection is the per-layer capacity variant, exactly"
        );
        assert_eq!(
            starved.recorded(),
            vec![FakeDeviceEvent::Attributes, FakeDeviceEvent::DeviceOptInCap],
            "cap rejection precedes the setter and every occupancy query"
        );
    }

    /// The opt-in ceiling is raised before occupancy is read, and a device that
    /// refuses to raise it is rejected rather than measured at the stale
    /// ceiling.
    ///
    /// This blake2 fixture's largest request (7,168 bytes) is under the 48 KiB
    /// default, so the refusal here is only observable from a starting ceiling
    /// below it; six corpus layouts request 69,632 bytes and exceed the
    /// default (see the corpus-geometry test), so in production the raise is
    /// load-bearing. The paired control proves the raise is what admits.
    #[test]
    fn cpu_dr_tail_resource_requires_raised_optin() {
        let artifact = artifact();
        let largest = plan_dr_tail_layers(
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            0,
            DEVICE_CAP,
            DrTailEntrySelection::Portable,
        )
        .expect("baseline plan")
        .iter()
        .map(DrTailLayerPlan::dynamic_smem_bytes)
        .max()
        .expect("non-empty");
        let starved_ceiling = largest - 1;

        let mut queries = FakeQueries::healthy(DEVICE_CAP);
        queries.attributes.borrow_mut().max_dynamic_smem_bytes = starved_ceiling;
        queries.grant_optin = false;
        let error = admit_dr_tail_resources(
            &queries,
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect_err("an unraised opt-in ceiling must reject");
        assert_eq!(
            error,
            DrTailResourceError::DynamicMemoryExceedsOptIn {
                required: largest,
                cap: starved_ceiling,
            }
        );
        assert_eq!(
            queries.recorded(),
            vec![
                FakeDeviceEvent::Attributes,
                FakeDeviceEvent::DeviceOptInCap,
                FakeDeviceEvent::SetMaxDynamicSmemBytes(largest),
                FakeDeviceEvent::Attributes,
            ],
            "a refused raise rejects before any occupancy query"
        );

        // Same starting ceiling, raise granted: the very same plan admits, so
        // the rejection above is the refusal and not the geometry.
        let queries = FakeQueries::healthy(DEVICE_CAP);
        queries.attributes.borrow_mut().max_dynamic_smem_bytes = starved_ceiling;
        let plan = admit_dr_tail_resources(
            &queries,
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect("a granted raise admits the same plan");
        assert_eq!(
            plan.resources().effective_max_dynamic_smem_bytes(),
            largest,
            "the ceiling is raised to exactly the largest selected request"
        );
    }

    #[test]
    fn cpu_dr_tail_resource_rejects_spill_and_zero_occupancy() {
        let artifact = artifact();
        let queries = FakeQueries::healthy(DEVICE_CAP);
        queries.attributes.borrow_mut().local_bytes = 16;
        assert!(matches!(
            admit_dr_tail_resources(
                &queries,
                artifact.as_ref(),
                FINAL_TRACE_LOG,
                DrTailEntrySelection::Portable
            ),
            Err(DrTailResourceError::LocalMemorySpill { .. })
        ));
        assert_eq!(
            queries.recorded(),
            vec![FakeDeviceEvent::Attributes],
            "a spill rejects at the first attribute read"
        );

        let distinct = distinct_selected_sizes(artifact.as_ref());
        let largest = *distinct.last().expect("non-empty");
        let mut queries = FakeQueries::healthy(DEVICE_CAP);
        queries.occupancy = 0;
        assert!(matches!(
            admit_dr_tail_resources(
                &queries,
                artifact.as_ref(),
                FINAL_TRACE_LOG,
                DrTailEntrySelection::Portable
            ),
            Err(DrTailResourceError::ZeroOccupancy { .. })
        ));
        assert_eq!(
            queries.recorded(),
            vec![
                FakeDeviceEvent::Attributes,
                FakeDeviceEvent::DeviceOptInCap,
                FakeDeviceEvent::SetMaxDynamicSmemBytes(largest),
                FakeDeviceEvent::Attributes,
                FakeDeviceEvent::Occupancy(distinct[0]),
            ],
            "zero occupancy rejects at the first measured size"
        );
    }

    /// The fake device records every interaction; the exact recorded sequence
    /// locks the admission order and counts: one initial attribute read, one
    /// cap read, exactly one setter call at the largest selected size, one
    /// effective-ceiling re-read, then one occupancy query per distinct
    /// selected size in ascending order — and nothing else.
    #[test]
    fn cpu_dr_tail_resource_admission_event_order() {
        let artifact = artifact();
        let queries = FakeQueries::healthy(DEVICE_CAP);
        let plan = admit_dr_tail_resources(
            &queries,
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect("healthy admission");

        let distinct = distinct_selected_sizes(artifact.as_ref());
        let largest = *distinct.last().expect("non-empty");
        let mut expected = vec![
            FakeDeviceEvent::Attributes,
            FakeDeviceEvent::DeviceOptInCap,
            FakeDeviceEvent::SetMaxDynamicSmemBytes(largest),
            FakeDeviceEvent::Attributes,
        ];
        expected.extend(
            distinct
                .iter()
                .map(|&bytes| FakeDeviceEvent::Occupancy(bytes)),
        );
        assert_eq!(queries.recorded(), expected);
        assert_eq!(
            plan.resources()
                .occupancy_by_dynamic_bytes()
                .iter()
                .map(|(bytes, _)| *bytes)
                .collect::<Vec<_>>(),
            distinct,
            "the plan records occupancy for exactly the measured sizes"
        );
    }

    fn distinct_selected_sizes(
        artifact: &GKRCircuitArtifact<gpu_core::primitives::field::BF>,
    ) -> Vec<usize> {
        let mut distinct: Vec<usize> = plan_dr_tail_layers(
            artifact,
            FINAL_TRACE_LOG,
            0,
            DEVICE_CAP,
            DrTailEntrySelection::Portable,
        )
        .expect("baseline plan")
        .iter()
        .map(DrTailLayerPlan::dynamic_smem_bytes)
        .collect();
        distinct.sort_unstable();
        distinct.dedup();
        distinct
    }

    /// Test 5 of C-corrections: the committed corpus at this geometry needs
    /// the opt-in raise. Six of the twelve layouts select 69,632-byte dynamic
    /// requests, above the 48 KiB architecture default; the blake2 unit
    /// fixture is the small outlier.
    #[test]
    fn cpu_dr_tail_resource_corpus_geometry_requires_optin_raise() {
        let mut per_layout_largest = Vec::new();
        for (layout_name, _) in CONTINUATION_GOLDEN_CORPUS {
            let layout_name: &'static str = layout_name;
            let (programs, _) = compile_corpus_layout(layout_name);
            let layers = plan_dr_tail_layers(
                programs.runtime_circuit().as_ref(),
                FINAL_TRACE_LOG,
                0,
                DEVICE_CAP,
                DrTailEntrySelection::Portable,
            )
            .unwrap_or_else(|error| panic!("{layout_name}: {error:?}"));
            let largest = layers
                .iter()
                .map(DrTailLayerPlan::dynamic_smem_bytes)
                .max()
                .expect("non-empty");
            per_layout_largest.push((layout_name, largest));
        }
        let corpus_largest = per_layout_largest
            .iter()
            .map(|(_, bytes)| *bytes)
            .max()
            .expect("non-empty corpus");
        assert_eq!(corpus_largest, 69_632);
        assert!(
            corpus_largest > 48 * 1024,
            "the opt-in raise is load-bearing for the committed corpus"
        );
        assert_eq!(
            per_layout_largest
                .iter()
                .filter(|(_, bytes)| *bytes == corpus_largest)
                .count(),
            6,
            "six layouts reach the corpus maximum"
        );
        assert_eq!(
            per_layout_largest
                .iter()
                .find(|(name, _)| *name == "blake2_with_extended_control_layout_gkr.json")
                .map(|(_, bytes)| *bytes),
            Some(7_168),
            "the unit-test fixture is the small geometry"
        );
    }

    /// A plan cannot be assembled outside `admit_dr_tail_resources`: its fields
    /// are private, so this test asserts the accessors are the only surface.
    #[test]
    fn cpu_dr_tail_resource_plan_is_admission_only() {
        let artifact = artifact();
        let plan = admit_dr_tail_resources(
            &FakeQueries::healthy(DEVICE_CAP),
            artifact.as_ref(),
            FINAL_TRACE_LOG,
            DrTailEntrySelection::Portable,
        )
        .expect("healthy admission");
        assert!(!plan.layers().is_empty());
        assert_eq!(plan.resources().local_bytes(), 0);
        let largest = plan
            .layers()
            .iter()
            .map(DrTailLayerPlan::dynamic_smem_bytes)
            .max()
            .expect("non-empty");
        assert!(plan.resources().effective_max_dynamic_smem_bytes() >= largest);
        for (dynamic_bytes, occupancy) in plan.resources().occupancy_by_dynamic_bytes() {
            assert!(*occupancy > 0);
            assert!(*dynamic_bytes <= plan.resources().effective_max_dynamic_smem_bytes());
        }
    }
}
