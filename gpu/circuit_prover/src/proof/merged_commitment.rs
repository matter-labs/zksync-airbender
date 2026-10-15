use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::upstream::{CommitmentMode, ProverConfig};
use gpu_core::primitives::device_tracing::Range;
use gpu_gkr::proof_layout::GpuGKRTraceGeometry;
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_gkr::stage1::GpuGKRStage1Output;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::holder::{WitnessCommitmentStrategy, WitnessPostCommitStorage};
use gpu_trace::trace::memory::{schedule_memory_commitment_job, MemoryCommitmentJob};
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};

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
        if let Some(it) = self.inits_and_teardowns.as_mut() {
            it.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(td) = self.tracing_data.as_mut() {
            td.schedule_transfer(&mut self.transfer, context)?;
        }
        self.transfer.record_transferred(context)
    }
}

pub fn commit_merged_from_transfers<'a, A: GoodAllocator + 'a>(
    gkr_programs: &GkrPrograms,
    prover_config: &ProverConfig,
    inputs: GpuGKRMergedCommitTransfer<'a, A>,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    assert_eq!(
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.whir_schedule.whir_steps_schedule[0]
    );
    inputs.transfer.ensure_transferred(context)?;
    let GpuGKRMergedCommitTransfer {
        transfer,
        setup,
        decoder,
        inits_and_teardowns,
        tracing_data,
    } = inputs;
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
    let geometry = GpuGKRTraceGeometry {
        log_domain_size: compiled_circuit.trace_len.trailing_zeros(),
        log_lde_factor: prover_config.lde_factor.trailing_zeros(),
        log_rows_per_leaf: prover_config.base_oracles_values_per_leaf.trailing_zeros(),
        log_tree_cap_size: prover_config.cap_size.trailing_zeros(),
    };
    let stream = context.get_exec_stream();
    let range = Range::new("commit_merged")?;
    range.start(stream)?;
    let mut stage1_output = GpuGKRStage1Output::generate(
        gkr_programs.circuit_type(),
        compiled_circuit,
        CommitmentMode::MergedMemoryAndWitness,
        geometry,
        Some(setup.trace_holder.get_hypercube_evals()),
        decoder.as_ref().map(|transfer| &transfer.data_device[..]),
        inits_and_teardowns
            .as_ref()
            .map(|transfer| &transfer.data_device),
        tracing_data.as_ref().map(|transfer| &transfer.data_device),
        None,
        WitnessCommitmentStrategy::AllCosets,
        WitnessPostCommitStorage::RawAndCosets,
        context,
    )?;
    let mut callbacks = transfer.into_callbacks();
    // The setup H2D reads pinned host memory the setup host owns.
    let setup_host = Arc::clone(&setup.host);
    callbacks.schedule(
        move || {
            let _ = &setup_host;
        },
        stream,
    )?;
    stage1_output.release_all_but_memory_trace_holder();
    drop(setup);
    drop(decoder);
    drop(inits_and_teardowns);
    drop(tracing_data);
    schedule_memory_commitment_job(
        &mut stage1_output.memory_trace_holder,
        callbacks,
        range,
        context,
    )
}
