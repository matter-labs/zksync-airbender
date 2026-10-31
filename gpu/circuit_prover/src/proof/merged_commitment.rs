use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, CommitmentMode, GKRCircuitArtifact, PrimeField,
    ProverConfig,
};
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::device_tracing::Range;
use gpu_gkr::proof_layout::GpuGKRTraceGeometry;
use gpu_gkr::setup::GpuGKRSetupTransfer;
use gpu_gkr::stage1::GpuGKRStage1Output;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::holder::{WitnessCommitmentStrategy, WitnessPostCommitStorage};
use gpu_trace::trace::memory::{schedule_memory_cap_readback, MemoryCommitmentJob};
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
/// Field-free merged routing and the generated base reader's f0/f1 limit.
pub fn validate_merged_packed_geometry(geometry: &BaseCommitmentGeometry) {
    assert_eq!(
        geometry.commitment_mode(),
        CommitmentMode::MergedMemoryAndWitness
    );
    assert!(
        geometry.values_per_leaf() <= 2,
        "GPU base opening verifier supports only fold_log2<=1 (one or two accumulators)"
    );
}

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

/// Bind the merged producer to its immutable config and logical artifact.
pub fn validate_merged_commitment_geometry<F: PrimeField>(
    config: &ProverConfig,
    geometry: &BaseCommitmentGeometry,
    circuit: &GKRCircuitArtifact<F>,
) {
    assert_eq!(
        config.commitment_mode,
        CommitmentMode::MergedMemoryAndWitness
    );
    let expected = BaseCommitmentGeometry::from_config(config, BaseColumns::of(circuit))
        .expect("invalid merged commitment config");
    assert_eq!(
        *geometry, expected,
        "merged commitment config/geometry mismatch"
    );
    validate_merged_packed_geometry(geometry);
    gpu_trace::trace::memory::validate_stage1_commitment_geometry(geometry, circuit);
}

/// Commit one concatenated memory/witness set using an explicitly bound shape.
/// Config-driven merged memory and worker entries use this same producer.
pub fn commit_merged_from_transfers_for_geometry<'a, A: GoodAllocator + 'a>(
    gkr_programs: &GkrPrograms,
    config: &ProverConfig,
    geometry: BaseCommitmentGeometry,
    inputs: GpuGKRMergedCommitTransfer<'a, A>,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    validate_merged_commitment_geometry(config, &geometry, gkr_programs.compiled_circuit());
    inputs.setup.host.validate_for_geometry(&geometry);
    gpu_trace::trace::holder::validate_baby_bear_base_geometry(
        &geometry,
        context
            .ntt_device_context()
            .whir_leaf_transform_params()
            .omega_log_order,
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
        WitnessCommitmentStrategy::AllCosets,
        WitnessPostCommitStorage::RawAndCosets,
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
    stage1.memory_trace_holder.commit_all(context)?;
    let job = schedule_memory_cap_readback(
        stage1.memory_trace_holder.unified_device_cap(),
        stage1
            .memory_trace_holder
            .base_commitment_geometry()
            .map(|(geometry, _)| geometry),
        stage1.memory_trace_holder.log_lde_factor,
        callbacks,
        Some(transfer.into_keepalive()),
        range,
        context,
    )?;
    Ok(job)
}
