use std::mem::size_of;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_gkr::proth120::backward::PreparedCoefficientTablesPr;
use gpu_gkr::proth120::base_layer_claims::BaseClaimIndicesPr;
use gpu_gkr::proth120::packed_challenges::{transcript_prefix_words, BOUNDARY_PREFIX_U32_LEN};
use gpu_gkr::setup::{L1WrapSetupHost, PackedSetupSource};
use gpu_hash::keccak256::Digest;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::packed::retained_len;
use gpu_trace::trace::tracing_data::{
    InitsAndTeardownsTransfer, TracingDataHost, TracingDataTransfer, UnrolledTracingDataHost,
};
use gpu_trace::witness::proth120::Proth120LookupRelations;
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceHost, UnifiedOpcodeTracingDataWithTimestamp,
    UnrolledUnifiedTraceHost, PAGE_SIZE_LOG2,
};

use super::{L1WrapConstantsHost, L1WrapGeometry};
use crate::proof::memory_policy::presets::l1_wrap::align_up;
use crate::upstream::{OperationMode, TimestampScalar};

pub(crate) const ALLOCATOR_BLOCK_BYTES: usize = 1 << 20;

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
    pub(crate) setup_reduction_layers: u32,
    pub(crate) constants: Arc<L1WrapConstantsHost>,
    pub(crate) relations: Proth120LookupRelations,
    pub(crate) coefficient_tables: PreparedCoefficientTablesPr,
    pub(crate) base_claim_indices: BaseClaimIndicesPr,
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
        setup_reduction_layers: u32,
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
        let relations = Proth120LookupRelations::allocate(&constants.relations, context)?;
        let coefficient_tables =
            PreparedCoefficientTablesPr::new(&constants.programs, &top_bits_host, context)?;
        let base_claim_indices =
            BaseClaimIndicesPr::allocate(&constants.base_claim_indices, context)?;
        let setup =
            PackedSetupSource::new(Arc::clone(&setup_host), setup_reduction_layers, context)?;
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
            setup_reduction_layers,
            constants,
            relations,
            coefficient_tables,
            base_claim_indices,
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
        self.coefficient_tables.stage_transfer(&mut self.transfer);
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        self.inits_and_teardowns
            .schedule_transfer(&mut self.transfer, context)?;
        self.tracing_data
            .schedule_transfer(&mut self.transfer, context)?;
        self.relations
            .schedule_transfer(&self.constants.relations, &mut self.transfer, context)?;
        self.base_claim_indices
            .schedule_transfer(&mut self.transfer, context)?;
        self.setup.schedule_transfer(&mut self.transfer, context)?;
        self.transfer.record_transferred(context)
    }

    /// Bytes the phase-one inputs take in the inputs reserve: every part rounded up
    /// to an allocator block.
    pub fn phase_one_capacity_bytes(
        geometry: &L1WrapGeometry,
        setup_reduction_layers: u32,
    ) -> usize {
        let circuit_type = geometry.circuit_type;
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
        let log_leaves =
            geometry.trace_log + geometry.pack_log2 - geometry.log_base_values_per_leaf;
        let parts = [
            bytes(
                trace_len,
                size_of::<UnifiedOpcodeTracingDataWithTimestamp>(),
            ),
            bytes(capacity >> PAGE_SIZE_LOG2, size_of::<u32>()),
            bytes(capacity, size_of::<u32>()),
            bytes(capacity, size_of::<TimestampScalar>()),
            bytes(decoder_entries, size_of::<ExecutorFamilyDecoderData>()),
            bytes(BOUNDARY_PREFIX_U32_LEN + num_sets, size_of::<u32>()),
            bytes(geometry.setup_columns * geometry.rows, size_of::<PR>()),
            bytes(
                geometry.packed_setup_columns * (geometry.rows << geometry.pack_log2),
                size_of::<PR>(),
            ),
            bytes(
                (1 << geometry.log_base_lde)
                    * retained_len(log_leaves, setup_reduction_layers.min(log_leaves)),
                size_of::<Digest>(),
            ),
        ];
        parts.iter().sum()
    }
}
