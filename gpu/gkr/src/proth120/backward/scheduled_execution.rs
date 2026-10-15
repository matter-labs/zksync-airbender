use std::cell::Cell;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

use super::banks::{
    schedule_coefficient_tables_upload_pr, CoefficientTablesHostPr, CoefficientTablesPr,
};
use super::dr_tail::DrTailProofPlanPr;
use super::eq::BackwardScratchPr;
use crate::backward::ClaimBufferLayout;
use crate::forward::GpuGKRTranscriptHandoff;
use crate::proth120::forward::ForwardToBackwardHandoffPr;
use crate::proth120::packed_challenges::PackedChallenges;
use crate::proth120::programs::GkrProgramsPr;
use crate::proth120::proof_layout::ProofSlabPr;
use crate::upstream::{GKRAddress, PR};
use crate::GpuGKRStorage;

#[doc(hidden)]
#[derive(Debug, PartialEq, Eq)]
pub struct GKRBackwardStageSnapshotPr {
    pub layer_idx: usize,
    pub seed: [u8; 32],
    pub claim_point: Vec<PR>,
    pub batching_challenge: PR,
    pub claims: BTreeMap<GKRAddress, PR>,
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceEventPr {
    Observed,
    Allocated,
    Cloned,
    LastReaderEnqueued,
    Released,
    HostKeepalive,
    Mark,
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ResourceIdPr {
    pub address: usize,
    pub bytes: usize,
}

impl ResourceIdPr {
    pub fn device<T>(slice: &DeviceSlice<T>) -> Self {
        Self {
            address: slice.as_ptr() as usize,
            bytes: slice.len() * size_of::<T>(),
        }
    }

    pub fn host<T>(slice: &[T]) -> Self {
        Self {
            address: slice.as_ptr() as usize,
            bytes: size_of_val(slice),
        }
    }
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResourceCountsPr {
    pub strong: usize,
    pub views: usize,
}

impl ResourceCountsPr {
    pub fn shared<T>(backing: &Arc<T>, views: usize) -> Self {
        Self {
            strong: Arc::strong_count(backing),
            views,
        }
    }

    pub fn released<T>(backing: &Arc<T>, views: usize) -> Self {
        Self {
            strong: Arc::strong_count(backing)
                .checked_sub(views)
                .expect("Proth120 resource ledger releases more views than strong references"),
            views,
        }
    }
}

#[doc(hidden)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResourceRecordPr {
    pub seq: usize,
    pub stage: &'static str,
    pub layer: Option<usize>,
    pub event: ResourceEventPr,
    pub owner: String,
    pub id: ResourceIdPr,
    pub counts: Option<ResourceCountsPr>,
    pub adjusted_live_bytes: usize,
    pub main_peak_bytes: usize,
}

#[doc(hidden)]
#[derive(Default)]
pub struct GKRBackwardStageSnapshotSinkPr {
    snapshots: Mutex<Vec<GKRBackwardStageSnapshotPr>>,
    resources: Mutex<Vec<ResourceRecordPr>>,
}

impl GKRBackwardStageSnapshotSinkPr {
    pub fn into_snapshots(self) -> Vec<GKRBackwardStageSnapshotPr> {
        self.into_parts().0
    }

    pub fn into_parts(self) -> (Vec<GKRBackwardStageSnapshotPr>, Vec<ResourceRecordPr>) {
        (
            self.snapshots
                .into_inner()
                .expect("Proth120 stage snapshot sink is poisoned"),
            self.resources
                .into_inner()
                .expect("Proth120 resource ledger is poisoned"),
        )
    }

    pub fn record(
        &self,
        context: &ProverContext,
        stage: &'static str,
        layer: Option<usize>,
        event: ResourceEventPr,
        owner: &str,
        id: ResourceIdPr,
        counts: Option<ResourceCountsPr>,
    ) {
        let adjusted_live_bytes = context.get_used_mem_current();
        let main_peak_bytes = context.get_used_mem_peak();
        let mut resources = self
            .resources
            .lock()
            .expect("Proth120 resource ledger is poisoned");
        let seq = resources.len();
        resources.push(ResourceRecordPr {
            seq,
            stage,
            layer,
            event,
            owner: owner.to_owned(),
            id,
            counts,
            adjusted_live_bytes,
            main_peak_bytes,
        });
    }
}

thread_local! {
    static RESOURCE_LEDGER: Cell<Option<UnsafeMutAccessor<GKRBackwardStageSnapshotSinkPr>>> =
        const { Cell::new(None) };
}

pub(crate) struct ResourceLedgerScopePr {
    previous: Option<UnsafeMutAccessor<GKRBackwardStageSnapshotSinkPr>>,
}

impl ResourceLedgerScopePr {
    pub(crate) fn enter(sink: Option<UnsafeMutAccessor<GKRBackwardStageSnapshotSinkPr>>) -> Self {
        let previous = RESOURCE_LEDGER.with(Cell::get);
        if sink.is_some() {
            RESOURCE_LEDGER.with(|ledger| ledger.set(sink));
        }
        Self { previous }
    }
}

impl Drop for ResourceLedgerScopePr {
    fn drop(&mut self) {
        RESOURCE_LEDGER.with(|ledger| ledger.set(self.previous));
    }
}

pub(crate) fn resource_ledger_active() -> bool {
    RESOURCE_LEDGER.with(Cell::get).is_some()
}

pub(crate) fn note_resource(
    context: &ProverContext,
    stage: &'static str,
    layer: Option<usize>,
    event: ResourceEventPr,
    owner: &str,
    id: ResourceIdPr,
    counts: Option<ResourceCountsPr>,
) {
    if let Some(sink) = RESOURCE_LEDGER.with(Cell::get) {
        unsafe { sink.get() }.record(context, stage, layer, event, owner, id, counts);
    }
}

pub(crate) fn note_device<T>(
    context: &ProverContext,
    stage: &'static str,
    layer: Option<usize>,
    event: ResourceEventPr,
    owner: &str,
    slice: &DeviceSlice<T>,
) {
    if let Some(sink) = RESOURCE_LEDGER.with(Cell::get) {
        unsafe { sink.get() }.record(
            context,
            stage,
            layer,
            event,
            owner,
            ResourceIdPr::device(slice),
            None,
        );
    }
}

pub(crate) fn note_storage_inventory(
    context: &ProverContext,
    stage: &'static str,
    layer: Option<usize>,
    event: ResourceEventPr,
    storage: &GpuGKRStorage<PR, PR>,
) {
    if !resource_ledger_active() {
        return;
    }
    let mut views: Vec<(String, &Arc<DeviceAllocation<PR>>)> = Vec::new();
    for (index, source) in storage.layers.iter().enumerate() {
        for (class, class_backing) in &source.base_class_backings {
            views.push((
                format!("storage.layer{index}.{class:?}.base"),
                &class_backing.backing,
            ));
        }
        for (class, backing) in &source.ext_class_backings {
            views.push((format!("storage.layer{index}.{class:?}.ext"), backing));
        }
        for poly in source.base_field_inputs.values() {
            views.push((format!("storage.layer{index}.base_poly"), &poly.backing));
        }
        for poly in source.extension_field_inputs.values() {
            views.push((format!("storage.layer{index}.ext_poly"), &poly.backing));
        }
    }
    let mut backings: BTreeMap<usize, (String, &Arc<DeviceAllocation<PR>>, usize)> =
        BTreeMap::new();
    for (owner, backing) in views {
        backings
            .entry(backing.as_ptr() as usize)
            .or_insert((owner, backing, 0))
            .2 += 1;
    }
    for (owner, backing, views) in backings.into_values() {
        let counts = if event == ResourceEventPr::Released {
            ResourceCountsPr::released(backing, views)
        } else {
            ResourceCountsPr::shared(backing, views)
        };
        note_resource(
            context,
            stage,
            layer,
            event,
            &owner,
            ResourceIdPr::device(backing),
            Some(counts),
        );
    }
}

pub(crate) struct LayerInputPr {
    pub(crate) seed: DeviceAllocation<u8>,
    pub(crate) point_and_batching: DeviceAllocation<PR>,
    pub(crate) claims: DeviceAllocation<PR>,
    pub(crate) claim_layout: ClaimBufferLayout,
}

pub(crate) struct ScheduledLayerExecutionPr {
    pub(crate) layer_idx: usize,
    pub(crate) _tracing_ranges: Vec<Range>,
    pub(crate) next: Option<LayerInputPr>,
}

impl ScheduledLayerExecutionPr {
    pub(crate) fn take_next(&mut self) -> LayerInputPr {
        self.next
            .take()
            .expect("Proth120 backward layer must return its next-layer input")
    }
}

pub(crate) fn gather_pr(
    sources: impl Iterator<Item = *const PR>,
    destination: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const _: () = assert!(size_of::<PR>() == size_of::<E4>());
    let pointers: Vec<u64> = sources.map(|pointer| pointer as u64).collect();
    assert!(
        pointers
            .iter()
            .all(|&pointer| pointer != 0 && pointer % 16 == 0),
        "Proth120 gather source pointers must be non-null and 16-byte aligned"
    );
    gpu_hash::blake2s::gather_e_addresses(
        &pointers,
        unsafe { destination.transmute_mut::<E4>() },
        stream,
    )
}

pub(crate) fn schedule_stage_snapshot_pr(
    layer_idx: usize,
    input: &LayerInputPr,
    output: UnsafeMutAccessor<GKRBackwardStageSnapshotSinkPr>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        input.claims.len(),
        input.claim_layout.claim_count(),
        "Proth120 stage snapshot claim layout mismatch"
    );
    assert_eq!(input.seed.len(), 32, "Proth120 stage snapshot seed length");
    let stream = context.get_exec_stream();
    let mut seed_host = unsafe { context.alloc_host_uninit_slice::<u8>(32) };
    let mut point_host =
        unsafe { context.alloc_host_uninit_slice::<PR>(input.point_and_batching.len()) };
    let mut claims_host = unsafe { context.alloc_host_uninit_slice::<PR>(input.claims.len()) };
    memory_copy_async(&mut seed_host, &input.seed, stream)?;
    memory_copy_async(&mut point_host, &input.point_and_batching, stream)?;
    memory_copy_async(&mut claims_host, &input.claims, stream)?;
    let seed_host = seed_host.get_accessor();
    let point_host = point_host.get_accessor();
    let claims_host = claims_host.get_accessor();
    let addresses = input.claim_layout.addresses.clone();
    callbacks.schedule(
        move || {
            let seed: [u8; 32] = unsafe { seed_host.get() }
                .try_into()
                .expect("Proth120 stage snapshot seed length");
            let (&batching_challenge, claim_point) = unsafe { point_host.get() }
                .split_last()
                .expect("Proth120 stage snapshot must contain a batching challenge");
            let claims = addresses
                .iter()
                .copied()
                .zip(unsafe { claims_host.get() }.iter().copied())
                .collect();
            unsafe { output.get() }
                .snapshots
                .lock()
                .expect("Proth120 stage snapshot sink is poisoned")
                .push(GKRBackwardStageSnapshotPr {
                    layer_idx,
                    seed,
                    claim_point: claim_point.to_vec(),
                    batching_challenge,
                    claims,
                });
        },
        stream,
    )
}

pub struct GpuGKRBackwardScheduledExecutionPr {
    pub(crate) _tracing_ranges: Vec<Range>,
    pub(crate) dimension_reducing_layers: Vec<ScheduledLayerExecutionPr>,
    pub(crate) main_layers: Vec<ScheduledLayerExecutionPr>,
    pub(crate) final_device_seed: Option<DeviceAllocation<u8>>,
    pub(crate) final_device_claim_point_and_batching: Option<DeviceAllocation<PR>>,
    pub(crate) final_device_claims: Option<DeviceAllocation<PR>>,
    pub(crate) final_claim_layout: Option<ClaimBufferLayout>,
    pub(crate) coefficient_tables: Option<CoefficientTablesPr>,
    #[allow(dead_code)]
    pub(crate) coefficient_upload_callbacks: Option<Callbacks<'static>>,
    pub(crate) scratch: Option<BackwardScratchPr>,
    pub(crate) _transcript_handoff: Option<GpuGKRTranscriptHandoff<PR>>,
}

impl GpuGKRBackwardScheduledExecutionPr {
    pub fn final_device_seed_and_claim_point_mut(
        &mut self,
    ) -> (&mut DeviceAllocation<u8>, &DeviceSlice<PR>) {
        let seed = self
            .final_device_seed
            .as_mut()
            .expect("Proth120 backward seed handoff buffer must be allocated before consumption");
        let point = self
            .final_device_claim_point_and_batching
            .as_ref()
            .expect("Proth120 backward claim point must be allocated before consumption");
        assert!(
            !point.is_empty(),
            "Proth120 final claim point must include the batching slot"
        );
        (seed, &point[..point.len() - 1])
    }

    pub fn final_claim_addresses(&self) -> &[GKRAddress] {
        &self
            .final_claim_layout
            .as_ref()
            .expect("Proth120 backward layer-0 claim layout must be set before consumption")
            .addresses
    }

    pub fn final_claims(&self) -> &DeviceSlice<PR> {
        self.final_device_claims
            .as_ref()
            .expect("Proth120 backward layer-0 claims must be allocated before consumption")
    }

    pub(crate) fn note_device_buffers(
        &self,
        context: &ProverContext,
        stage: &'static str,
        event: ResourceEventPr,
    ) {
        if !resource_ledger_active() {
            return;
        }
        if let Some(seed) = self.final_device_seed.as_ref() {
            note_device(context, stage, None, event, "bwd.final_seed", seed);
        }
        if let Some(point) = self.final_device_claim_point_and_batching.as_ref() {
            note_device(context, stage, None, event, "bwd.final_point", point);
        }
        if let Some(claims) = self.final_device_claims.as_ref() {
            note_device(context, stage, None, event, "bwd.final_claims", claims);
        }
        if let Some(tables) = self.coefficient_tables.as_ref() {
            tables.note_resources(context, stage, event);
        }
        if let Some(scratch) = self.scratch.as_ref() {
            scratch.note_resources(context, stage, event);
        }
    }

    pub fn release_device_buffers(&mut self) {
        self.final_device_seed = None;
        self.final_device_claim_point_and_batching = None;
        self.final_device_claims = None;
        self.coefficient_tables = None;
        self.scratch = None;
        for layer in self
            .dimension_reducing_layers
            .iter_mut()
            .chain(self.main_layers.iter_mut())
        {
            layer.next = None;
        }
    }
}

#[allow(clippy::too_many_arguments, clippy::needless_pass_by_value)]
pub fn schedule_backward_pr(
    handoff: ForwardToBackwardHandoffPr,
    inits_and_teardowns_top_bits: Vec<u32>,
    programs: Arc<GkrProgramsPr>,
    dr_tail_plan: &DrTailProofPlanPr,
    challenges: &PackedChallenges,
    proof: &mut ProofSlabPr,
    stage_snapshots: Option<UnsafeMutAccessor<GKRBackwardStageSnapshotSinkPr>>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<GpuGKRBackwardScheduledExecutionPr> {
    let ForwardToBackwardHandoffPr {
        transcript_handoff,
        mut backward_state,
        d_seed,
        d_evaluation_point_and_batching,
        top_layer_claim_layout,
        initial_d_claims,
        post_forward_handoff_range,
    } = handoff;
    let _ledger = ResourceLedgerScopePr::enter(stage_snapshots);
    note_storage_inventory(
        context,
        "backward",
        None,
        ResourceEventPr::Observed,
        &backward_state.storage,
    );
    dr_tail_plan.validate_before_enqueue(&programs, 4, context);
    let stream = context.get_exec_stream();
    let mut tracing_ranges = std::mem::take(&mut backward_state.forward_tracing_ranges);
    tracing_ranges.push(post_forward_handoff_range);
    let workflow_range = Range::new("gkr.proth120.backward.schedule")?;
    workflow_range.start(stream)?;
    let host = CoefficientTablesHostPr::build(&programs, &inits_and_teardowns_top_bits);
    let (coefficient_tables, coefficient_upload_callbacks) =
        schedule_coefficient_tables_upload_pr(&host, context)?;
    let mut scratch = BackwardScratchPr::new(context)?;
    let mut input = LayerInputPr {
        seed: d_seed,
        point_and_batching: d_evaluation_point_and_batching,
        claims: initial_d_claims,
        claim_layout: top_layer_claim_layout,
    };
    if let Some(output) = stage_snapshots {
        let initial_layer_idx = backward_state
            .pending_layers
            .front()
            .map_or(programs.runtime_circuit.layers.len(), |(layer_idx, _)| {
                layer_idx + 1
            });
        schedule_stage_snapshot_pr(initial_layer_idx, &input, output, callbacks, context)?;
    }
    let dimension_reducing_range = Range::new("gkr.proth120.backward.dimension_reducing_layers")?;
    dimension_reducing_range.start(stream)?;
    let mut cursor = dr_tail_plan.cursor();
    let mut dimension_reducing_layers = Vec::new();
    while let Some(plan) = backward_state.prepare_next_layer_pr(&mut cursor) {
        let mut execution = plan.schedule_execute_pr(
            input,
            dr_tail_plan,
            &mut backward_state.storage,
            proof,
            context,
        )?;
        input = execution.take_next();
        if let Some(output) = stage_snapshots {
            schedule_stage_snapshot_pr(execution.layer_idx, &input, output, callbacks, context)?;
        }
        note_resource(
            context,
            "backward.dr",
            Some(execution.layer_idx),
            ResourceEventPr::Mark,
            "layer_enqueued",
            ResourceIdPr::default(),
            None,
        );
        dimension_reducing_layers.push(execution);
    }
    cursor.finish();
    note_storage_inventory(
        context,
        "backward.dr",
        None,
        ResourceEventPr::Observed,
        &backward_state.storage,
    );
    dimension_reducing_range.end(stream)?;
    tracing_ranges.push(dimension_reducing_range);
    let mut main_state = backward_state.into_main_layer_backward_state_pr(
        &inits_and_teardowns_top_bits,
        Arc::clone(&programs),
        &proof.layout,
    );
    tracing_ranges.append(&mut main_state.forward_tracing_ranges);
    let main_range = Range::new("gkr.proth120.backward.main_layers")?;
    main_range.start(stream)?;
    let mut main_layers = Vec::new();
    while let Some(mut plan) =
        main_state.prepare_next_layer_pr(&coefficient_tables, &mut scratch, context)?
    {
        let release_scratch = main_state.scratch_last_reader == Some(plan.layer_idx);
        let mut execution = plan.schedule_execute_pr(
            input,
            &coefficient_tables,
            challenges,
            &mut main_state.storage,
            proof,
            &mut scratch,
            release_scratch,
            context,
        )?;
        drop(plan);
        input = execution.take_next();
        if let Some(output) = stage_snapshots {
            schedule_stage_snapshot_pr(execution.layer_idx, &input, output, callbacks, context)?;
        }
        note_storage_inventory(
            context,
            "backward.main",
            Some(execution.layer_idx),
            ResourceEventPr::Observed,
            &main_state.storage,
        );
        main_layers.push(execution);
    }
    main_range.end(stream)?;
    tracing_ranges.push(main_range);
    note_storage_inventory(
        context,
        "backward.main",
        None,
        ResourceEventPr::Released,
        &main_state.storage,
    );
    drop(main_state);
    note_resource(
        context,
        "backward",
        None,
        ResourceEventPr::Mark,
        "main_state_dropped",
        ResourceIdPr::default(),
        None,
    );
    workflow_range.end(stream)?;
    tracing_ranges.push(workflow_range);
    let LayerInputPr {
        seed,
        point_and_batching,
        claims,
        claim_layout,
    } = input;
    let execution = GpuGKRBackwardScheduledExecutionPr {
        _tracing_ranges: tracing_ranges,
        dimension_reducing_layers,
        main_layers,
        final_device_seed: Some(seed),
        final_device_claim_point_and_batching: Some(point_and_batching),
        final_device_claims: Some(claims),
        final_claim_layout: Some(claim_layout),
        coefficient_tables: Some(coefficient_tables),
        coefficient_upload_callbacks: Some(coefficient_upload_callbacks),
        scratch: Some(scratch),
        _transcript_handoff: Some(transcript_handoff),
    };
    execution.note_device_buffers(context, "backward", ResourceEventPr::Observed);
    Ok(execution)
}
