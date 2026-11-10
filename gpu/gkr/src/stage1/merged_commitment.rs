use gpu_trace::trace::memory::PartialTreeBuffer;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use super::GpuGKRStage1Output;
use crate::proof_layout::GpuGKRTraceGeometry;
use crate::setup::GpuGKRSetupTransfer;
use crate::upstream::{BaseColumns, BaseCommitmentGeometry, CommitmentMode, ProverConfig};
use crate::GkrPrograms;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::device_tracing::Range;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::holder::PartialTreePolicy;
use gpu_trace::trace::holder::{WitnessCommitmentStrategy, WitnessPostCommitStorage};
use gpu_trace::trace::memory::{
    schedule_memory_commitment_job, schedule_memory_commitment_job_in_place,
    schedule_memory_commitment_job_with_monomials, MemoryCommitmentJob,
};
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};

/// Shared H2D ownership for the existing BF memory-and-witness generator.
pub struct GpuGKRMergedCommitTransfer<'a, A: GoodAllocator> {
    transfer: Transfer<'a>,
    setup: GpuGKRSetupTransfer<'a>,
    decoder: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
    tracing_data: Option<TracingDataTransfer<'a, A>>,
}

impl<'a, A: GoodAllocator + 'a> GpuGKRMergedCommitTransfer<'a, A> {
    pub fn new(
        setup: GpuGKRSetupTransfer<'a>,
        decoder: Option<DecoderTableTransfer<'a>>,
        inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
        tracing_data: Option<TracingDataTransfer<'a, A>>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let transfer = Transfer::new()?;
        // This fence follows every input allocation and the setup tail memset.
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            setup,
            decoder,
            inits_and_teardowns,
            tracing_data,
        })
    }

    pub fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.setup.schedule_transfer(&mut self.transfer, context)?;
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(inits) = self.inits_and_teardowns.as_mut() {
            inits.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(trace) = self.tracing_data.as_mut() {
            trace.schedule_transfer(&mut self.transfer, context)?;
        }
        self.transfer.record_transferred(context)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MergedCommitStrategy {
    AllCosets,
    InPlace,
    Monomials,
}

/// Commit one concatenated memory/witness set in the base geometry of a merged `config`.
pub fn commit_merged_from_transfers<'a, A: GoodAllocator + 'a>(
    gkr_programs: &GkrPrograms,
    config: &ProverConfig,
    inputs: GpuGKRMergedCommitTransfer<'a, A>,
    strategy: MergedCommitStrategy,
    partial_trees: PartialTreePolicy,
    partial_tree_buffer: Option<PartialTreeBuffer<A>>,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a, A>> {
    assert_eq!(
        config.commitment_mode,
        CommitmentMode::MergedMemoryAndWitness,
        "the merged producer requires a merged config"
    );
    let geometry = BaseCommitmentGeometry::from_config(
        config,
        BaseColumns::of(gkr_programs.compiled_circuit()),
    );

    inputs.transfer.ensure_transferred(context)?;
    let GpuGKRMergedCommitTransfer {
        transfer,
        setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
    } = inputs;
    let stream = context.get_exec_stream();
    let range = Range::new("commit_merged")?;
    range.start(stream)?;
    let trace_geometry = GpuGKRTraceGeometry {
        log_domain_size: u32::try_from(geometry.trace_len_log2()).expect("trace log2 exceeds u32"),
        log_lde_factor: geometry.lde_factor().trailing_zeros(),
        log_rows_per_leaf: geometry.values_per_leaf().trailing_zeros(),
        log_tree_cap_size: geometry.cap_size().trailing_zeros(),
    };
    let (commitment, storage) = match strategy {
        MergedCommitStrategy::AllCosets => (
            WitnessCommitmentStrategy::AllCosets,
            WitnessPostCommitStorage::RawAndCosets,
        ),
        MergedCommitStrategy::InPlace => (
            WitnessCommitmentStrategy::InPlace,
            WitnessPostCommitStorage::RawEvaluations,
        ),
        MergedCommitStrategy::Monomials => (
            WitnessCommitmentStrategy::PerCoset,
            WitnessPostCommitStorage::RawAndMonomials,
        ),
    };
    let mut stage1 = GpuGKRStage1Output::generate_for_geometry(
        gkr_programs.circuit_type(),
        gkr_programs.compiled_circuit(),
        trace_geometry,
        geometry,
        Some(setup.trace_holder.get_hypercube_evals()),
        decoder.as_ref().map(|input| &input.data_device[..]),
        inits_and_teardowns.as_ref().map(|input| &input.data_device),
        tracing_data.as_ref().map(|input| &input.data_device),
        None,
        commitment,
        storage,
        partial_trees,
        context,
    )?;
    let mut callbacks = Callbacks::new();
    let setup_host = Arc::clone(&setup.host);
    callbacks.schedule(
        move || {
            let _ = &setup_host;
        },
        stream,
    )?;
    stage1.release_all_but_memory_trace_holder();
    let inputs = Some(transfer.into_keepalive());
    match strategy {
        MergedCommitStrategy::AllCosets => schedule_memory_commitment_job(
            &mut stage1.memory_trace_holder,
            callbacks,
            inputs,
            range,
            context,
        ),
        MergedCommitStrategy::InPlace => schedule_memory_commitment_job_in_place(
            &mut stage1.memory_trace_holder,
            callbacks,
            inputs,
            range,
            context,
        ),
        MergedCommitStrategy::Monomials => schedule_memory_commitment_job_with_monomials(
            &mut stage1.memory_trace_holder,
            callbacks,
            inputs,
            range,
            partial_tree_buffer,
            context,
        ),
    }
}
