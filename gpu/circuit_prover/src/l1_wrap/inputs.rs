use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_gkr::proth120::packed_challenges::transcript_prefix_words;
use gpu_gkr::setup::{L1WrapSetupHost, PackedSetupSource};
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::tracing_data::{
    InitsAndTeardownsTransfer, TracingDataHost, TracingDataTransfer, UnrolledTracingDataHost,
};
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceHost, UnrolledUnifiedTraceHost,
};

use super::{L1WrapConstantsHost, L1WrapGeometry};
use crate::upstream::OperationMode;

pub struct L1WrapInputs<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: InitsAndTeardownsTransfer<'a, A>,
    pub(crate) tracing_data: TracingDataTransfer<'a, A>,
    pub(crate) transcript_prefix: DeviceAllocation<u32>,
    pub(crate) transcript_prefix_host: Vec<u32>,
    pub(crate) top_bits_host: Vec<u32>,
    pub(crate) setup_host: Arc<L1WrapSetupHost>,
    pub(crate) setup: PackedSetupSource<'a>,
    pub(crate) constants: Arc<L1WrapConstantsHost>,
    pub(crate) request_range: Option<Range>,
}

impl<'a, A: GoodAllocator + 'a> L1WrapInputs<'a, A> {
    pub fn new(
        geometry: &L1WrapGeometry,
        decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
        inits_and_teardowns: InitsAndTeardownsTraceHost<A>,
        tracing_data: UnrolledUnifiedTraceHost<A>,
        setup_host: Arc<L1WrapSetupHost>,
        constants: Arc<L1WrapConstantsHost>,
        operation_mode: &OperationMode,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let circuit_type = geometry.circuit_type;
        let num_sets = geometry.num_it_sets;
        let trace_len = geometry.rows;
        let top_bits_host = inits_and_teardowns.top_bits.clone();
        assert!(
            top_bits_host.len() == num_sets,
            "{circuit_type:?} requires {num_sets} inits-and-teardowns top bits, got {}",
            top_bits_host.len()
        );
        let decoder = decoder_host
            .map(|host| DecoderTableTransfer::new(host, context))
            .transpose()?;
        let inits_and_teardowns = InitsAndTeardownsTransfer::new(
            Some(inits_and_teardowns),
            num_sets,
            trace_len,
            context,
        )?;
        let tracing_data = TracingDataTransfer::new(
            TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(tracing_data)),
            trace_len,
            context,
        )?;
        let transcript_prefix_host = transcript_prefix_words(operation_mode, &top_bits_host);
        let transcript_prefix =
            context.alloc::<u32>(transcript_prefix_host.len(), AllocationPlacement::BestFit)?;
        let setup = PackedSetupSource::new(Arc::clone(&setup_host), context)?;
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
            transcript_prefix,
            transcript_prefix_host,
            top_bits_host,
            setup_host,
            setup,
            constants,
            request_range: None,
        })
    }

    /// `range` was started on `exec_stream` before these inputs were built;
    /// `prove()` ends it after the proof readback.
    pub fn time_request(&mut self, range: Range) {
        self.request_range = Some(range);
    }

    pub fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.transfer
            .stage(&self.transcript_prefix_host, &mut self.transcript_prefix);
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        self.inits_and_teardowns
            .schedule_transfer(&mut self.transfer, context)?;
        self.tracing_data
            .schedule_transfer(&mut self.transfer, context)?;
        self.setup.schedule_transfer(&mut self.transfer, context)?;
        self.transfer.record_transferred(context)
    }
}
