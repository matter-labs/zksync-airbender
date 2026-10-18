use std::mem::size_of;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_gkr::setup::L1WrapSetupHost;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::tracing_data::{
    InitsAndTeardownsTransfer, TracingDataHost, TracingDataTransfer, UnrolledTracingDataHost,
};
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceHost, UnifiedOpcodeTracingDataWithTimestamp,
    UnrolledUnifiedTraceHost, PAGE_SIZE_LOG2,
};

use super::L1WrapGeometry;
use crate::proof::memory_policy::presets::l1_wrap::align_up;
use crate::upstream::TimestampScalar;

pub(crate) const ALLOCATOR_BLOCK_BYTES: usize = 1 << 20;

pub struct L1WrapInputs<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: InitsAndTeardownsTransfer<'a, A>,
    pub(crate) tracing_data: TracingDataTransfer<'a, A>,
    pub(crate) top_bits: DeviceAllocation<u32>,
    pub(crate) top_bits_host: Vec<u32>,
    pub(crate) setup_host: Arc<L1WrapSetupHost>,
    pub(crate) request_range: Option<Range>,
}

const fn bytes(count: usize, element_bytes: usize) -> usize {
    align_up(
        count
            .checked_mul(element_bytes)
            .expect("L1Wrap phase-one capacity overflow"),
        ALLOCATOR_BLOCK_BYTES,
    )
}

impl<'a, A: GoodAllocator + 'a> L1WrapInputs<'a, A> {
    pub fn new(
        geometry: &L1WrapGeometry,
        decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
        inits_and_teardowns: InitsAndTeardownsTraceHost<A>,
        tracing_data: UnrolledUnifiedTraceHost<A>,
        setup_host: Arc<L1WrapSetupHost>,
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
        let top_bits = context.alloc::<u32>(top_bits_host.len(), AllocationPlacement::BestFit)?;
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
            top_bits,
            top_bits_host,
            setup_host,
            request_range: None,
        })
    }

    /// `range` was started on `exec_stream` before these inputs were built;
    /// `prove()` ends it after the proof readback.
    pub fn time_request(&mut self, range: Range) {
        self.request_range = Some(range);
    }

    pub fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.stage(&self.top_bits_host, &mut self.top_bits);
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        self.inits_and_teardowns
            .schedule_transfer(&mut self.transfer, context)?;
        self.tracing_data
            .schedule_transfer(&mut self.transfer, context)?;
        self.transfer.record_transferred(context)
    }

    pub const fn phase_one_capacity_bytes(circuit_type: CircuitType) -> usize {
        assert!(
            circuit_type.is_l1_wrap(),
            "L1Wrap phase-one capacity requires an L1 wrap circuit type"
        );
        let num_sets = circuit_type.get_num_inits_and_teardowns_sets();
        let trace_len = circuit_type.get_domain_size();
        let decoder_entries = circuit_type.rom().word_size();
        let capacity = num_sets
            .checked_mul(trace_len)
            .expect("L1Wrap phase-one capacity overflow");
        let parts = [
            bytes(
                trace_len,
                size_of::<UnifiedOpcodeTracingDataWithTimestamp>(),
            ),
            bytes(capacity >> PAGE_SIZE_LOG2, size_of::<u32>()),
            bytes(capacity, size_of::<u32>()),
            bytes(capacity, size_of::<TimestampScalar>()),
            bytes(decoder_entries, size_of::<ExecutorFamilyDecoderData>()),
            bytes(num_sets, size_of::<u32>()),
        ];
        let mut total = 0usize;
        let mut index = 0;
        while index < parts.len() {
            total = total
                .checked_add(parts[index])
                .expect("L1Wrap phase-one capacity overflow");
            index += 1;
        }
        total
    }
}
