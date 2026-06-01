use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use era_cudart::event::CudaEvent;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{ClaimBufferLayout, GpuGKRBackwardScheduledExecution};
use crate::prover::gkr::base_layer_claims::GpuGKRBaseLayerClaimsScheduledExecution;
use crate::prover::gkr::setup::GpuGKRForwardSetupHostKeepalive;
use crate::prover::gkr::stage1::GpuGKRStage1Keepalive;
use crate::prover::proof::inputs::GpuGKRProofTransferKeepalive;
use crate::prover::whir::fold::GpuWhirFoldScheduledExecution;
use crate::upstream::{DefaultTreeConstructor, Field, GKRCircuitArtifact, GKRProof, OutputType};

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
    /// shared `Transfer`'s accumulated `Callbacks`. Replaces the prior per-piece
    /// keepalive fields (`_setup`, `_memory`, `_external_challenges_*`,
    /// `_initial_transcript_canonical_top_bits_host`).
    pub(super) _inputs: GpuGKRProofTransferKeepalive<'a, A>,
    pub(super) _forward_setup: GpuGKRForwardSetupHostKeepalive<E4>,
    pub(super) _backward: GpuGKRBackwardScheduledExecution<BF, E4>,
    pub(super) _base_layer_claims: GpuGKRBaseLayerClaimsScheduledExecution<E4>,
    pub(super) _whir: GpuWhirFoldScheduledExecution,
    /// Device-resident WHIR base batching-challenge buffer drawn from the
    /// rolling backward seed before WHIR fold. Kept alive on the proof-job
    /// keepalive so any scheduled kernel still reading from it remains valid
    /// until `finish()` syncs the exec stream.
    #[allow(dead_code)]
    pub(super) _whir_batching_challenge_device: DeviceAllocation<E4>,
    /// Pinned host mirror of the device-resident proof slab (Phase 4). Populated
    /// by the terminal D2H; read by the single assembly callback.
    #[allow(dead_code)]
    pub(super) _proof_host_mirror: Option<HostAllocation<[u8]>>,
    /// Proof slab itself — held here so it outlives all scheduled writes and
    /// the terminal D2H.
    #[allow(dead_code)]
    pub(super) _proof_slab: Arc<DeviceAllocation<E4>>,
}

pub struct GpuGKRProofJob<'a, A: GoodAllocator> {
    pub(crate) is_finished_event: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
    pub(crate) proof: Box<Option<GKRProof<BF, E4, DefaultTreeConstructor>>>,
    pub(crate) ranges: Vec<Range>,
    pub(super) keepalive: GpuGKRProofJobKeepalive<'a, A>,
}

impl<'a, A: GoodAllocator> GpuGKRProofJob<'a, A> {
    #[cfg(test)]
    pub(crate) fn is_finished(&self) -> CudaResult<bool> {
        self.is_finished_event.query()
    }

    pub fn finish(self) -> CudaResult<(GKRProof<BF, E4, DefaultTreeConstructor>, f32)> {
        let Self {
            is_finished_event,
            callbacks,
            mut proof,
            ranges,
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

        Ok((proof, proof_time_ms))
    }
}

pub(crate) fn top_layer_claim_layout(
    output_layer_for_sumcheck: &BTreeMap<
        OutputType,
        prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput,
    >,
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

    grand_product_accumulator_computed
}

pub fn canonical_inits_and_teardowns_top_bits(
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> Vec<u32> {
    (0..compiled_circuit.memory_layout.teardown_sets.len() as u32).collect()
}
