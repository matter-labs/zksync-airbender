use std::collections::{BTreeMap, BTreeSet};

use era_cudart::event::CudaEvent;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::proof::inputs::GpuGKRProofTransferKeepalive;
use crate::upstream::{
    DefaultTreeConstructor, DimensionReducingInputOutput, Field, GKRCircuitArtifact, GKRProof,
    OutputType,
};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::HostAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
#[cfg(test)]
use gpu_gkr::backward::GKRBackwardStageSnapshot;
use gpu_gkr::backward::{
    ClaimBufferLayout, GKRBackwardStageSnapshotSink, GpuGKRBackwardScheduledExecution,
};
use gpu_gkr::base_layer_claims::GpuGKRBaseLayerClaimsScheduledExecution;
use gpu_gkr::setup::GpuGKRForwardSetupHostKeepalive;
use gpu_gkr::stage1::GpuGKRStage1Keepalive;
use gpu_whir::fold::GpuWhirFoldScheduledExecution;

mod backward;
pub(super) mod stage1_forward;
mod terminal;
mod whir;

pub(super) use backward::{
    prepare_backward_handoff, schedule_backward_phase, BackwardPhaseResult,
    ForwardToBackwardHandoff,
};
pub(super) use stage1_forward::{prepare_stage1_and_forward_setup, Stage1AndForwardPreparation};
pub(super) use terminal::schedule_terminal_proof_assembly;
pub(super) use whir::{schedule_whir_phase, WhirPhaseResult};

pub(super) struct GpuGKRProofJobKeepalive<'a, A: GoodAllocator> {
    pub(super) _stage1: GpuGKRStage1Keepalive,
    /// Holds every per-piece transfer wrapper (setup, decoder, inits_and_teardowns,
    /// tracing_data, memory caps, canonical_top_bits, external_challenges) plus the
    /// shared `Transfer`'s accumulated `Callbacks`.
    pub(super) _inputs: GpuGKRProofTransferKeepalive<'a, A>,
    pub(super) _forward_setup: GpuGKRForwardSetupHostKeepalive,
    pub(super) _backward: GpuGKRBackwardScheduledExecution,
    pub(super) _base_layer_claims: GpuGKRBaseLayerClaimsScheduledExecution,
    pub(super) _whir: GpuWhirFoldScheduledExecution,
    /// Pinned host mirror of the device-resident proof slab. Populated
    /// by the terminal D2H; read by the single assembly callback. This is the
    /// only buffer (host, pinned) the keepalive still owns past prove-end — the
    /// device reservations (proof slab, WHIR caps/ephemerals, batching
    /// challenge, backward handoff buffers) are released stream-ordered at the
    /// end of `prove()`.
    pub(super) _proof_host_mirror: Option<HostAllocation<[u8]>>,
}

type FinishedProof = GKRProof<BF, E4, DefaultTreeConstructor>;
type FinishedProofWithSnapshots = (
    FinishedProof,
    Option<Box<GKRBackwardStageSnapshotSink>>,
    f32,
);
#[cfg(test)]
type StagewiseFinishedProof = (FinishedProof, Vec<GKRBackwardStageSnapshot>, f32);

pub struct GpuGKRProofJob<'a, A: GoodAllocator> {
    pub(crate) is_finished_event: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
    pub(crate) proof: Box<Option<GKRProof<BF, E4, DefaultTreeConstructor>>>,
    pub(crate) ranges: Vec<Range>,
    pub(crate) stage_snapshots: Option<Box<GKRBackwardStageSnapshotSink>>,
    pub(super) keepalive: GpuGKRProofJobKeepalive<'a, A>,
}

impl<'a, A: GoodAllocator> GpuGKRProofJob<'a, A> {
    fn finish_inner(self) -> CudaResult<FinishedProofWithSnapshots> {
        let Self {
            is_finished_event,
            callbacks,
            mut proof,
            ranges,
            stage_snapshots,
            keepalive,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        drop(keepalive);
        let proof = proof
            .take()
            .expect("proof must be materialized before finish");
        let proof_time_ms = ranges
            .last()
            .expect("proof job must keep the top-level range")
            .elapsed()?;

        Ok((proof, stage_snapshots, proof_time_ms))
    }

    pub fn finish(self) -> CudaResult<(GKRProof<BF, E4, DefaultTreeConstructor>, f32)> {
        let (proof, _, proof_time_ms) = self.finish_inner()?;
        Ok((proof, proof_time_ms))
    }

    #[cfg(test)]
    pub(crate) fn finish_stagewise(self) -> CudaResult<StagewiseFinishedProof> {
        let (proof, snapshots, proof_time_ms) = self.finish_inner()?;
        Ok((
            proof,
            snapshots
                .expect("stagewise proof job must collect snapshots")
                .into_snapshots(),
            proof_time_ms,
        ))
    }
}

pub(crate) fn top_layer_claim_layout(
    output_layer_for_sumcheck: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> ClaimBufferLayout {
    let mut addresses = BTreeSet::new();
    let permutation_output = &output_layer_for_sumcheck[&OutputType::PermutationProduct];
    addresses.insert(permutation_output.output[0]);
    addresses.insert(permutation_output.output[1]);
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::Lookup16Bits) {
        addresses.insert(output.output[0]);
        addresses.insert(output.output[1]);
    }
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::LookupTimestamps) {
        addresses.insert(output.output[0]);
        addresses.insert(output.output[1]);
    }
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::GenericLookup) {
        addresses.insert(output.output[0]);
        addresses.insert(output.output[1]);
    }
    // Unified circuit: the inline inits/teardowns grand product adds a
    // second top-layer product channel. Mirror the CPU top_layer_claims insert
    // at prover/src/gkr/prover/mod.rs:556-559 (claim_initset @ output[0],
    // claim_teardownset @ output[1]) so every output_layer_for_sumcheck entry
    // has a claim address and the backward claim_idx lookup never panics.
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::InitsAndTeardownsProduct) {
        addresses.insert(output.output[0]);
        addresses.insert(output.output[1]);
    }
    ClaimBufferLayout::from_addresses(addresses.into_iter().collect())
}

pub(crate) fn grand_product_accumulator_from_explicit_evaluations(
    final_explicit_evaluations: &BTreeMap<OutputType, [Vec<E4>; 2]>,
) -> E4 {
    let [read_set_computed, write_set_computed] = final_explicit_evaluations
        .get(&OutputType::PermutationProduct)
        .expect("must contain permutation-product outputs")
        .clone()
        .map(|els| {
            let mut result = E4::ONE;
            for el in els.iter() {
                result.mul_assign(el);
            }
            result
        });
    let mut grand_product_accumulator_computed = write_set_computed;
    grand_product_accumulator_computed.mul_assign(
        &read_set_computed
            .inverse()
            .expect("read-set accumulator must not be zero"),
    );

    // Unified circuit: fold the inline inits/teardowns product into the
    // accumulator so the caller's `initial_contribution * accumulator == ONE`
    // closure holds as a single check. Exact mirror of the CPU prover at
    // prover/src/gkr/prover/mod.rs:813-823 — it_evals[0] = init_set,
    // it_evals[1] = teardown_set, contribution = teardown * init.inverse().
    if let Some(it_evals) = final_explicit_evaluations.get(&OutputType::InitsAndTeardownsProduct) {
        let [init_set_computed, teardown_set_computed] = it_evals.clone().map(|els| {
            let mut result = E4::ONE;
            for el in els.iter() {
                result.mul_assign(el);
            }
            result
        });
        let mut it_contribution = teardown_set_computed;
        it_contribution.mul_assign(
            &init_set_computed
                .inverse()
                .expect("init-set accumulator must not be zero"),
        );
        grand_product_accumulator_computed.mul_assign(&it_contribution);
    }

    grand_product_accumulator_computed
}

pub fn canonical_inits_and_teardowns_top_bits(
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> Vec<u32> {
    (0..compiled_circuit.memory_layout.teardown_sets.len() as u32).collect()
}
