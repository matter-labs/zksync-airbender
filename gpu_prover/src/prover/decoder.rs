use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::allocator::tracker::AllocationPlacement;
use crate::prover::context::{DeviceAllocation, ProverContext};
use crate::prover::transfer::Transfer;
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use era_cudart::result::CudaResult;
use std::sync::Arc;

pub(crate) struct DecoderTableTransfer<'a> {
    pub(crate) data_host: Arc<Vec<ExecutorFamilyDecoderData, ConcurrentStaticHostAllocator>>,
    pub(crate) data_device: DeviceAllocation<ExecutorFamilyDecoderData>,
    pub(crate) transfer: Transfer<'a>,
}

impl DecoderTableTransfer<'_> {
    pub(crate) fn new(
        data_host: Arc<Vec<ExecutorFamilyDecoderData, ConcurrentStaticHostAllocator>>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let transfer = Transfer::new()?;
        let data_device = context.alloc(data_host.len(), AllocationPlacement::Bottom)?;
        transfer.record_allocated(context)?;
        Ok(Self {
            data_host,
            data_device,
            transfer,
        })
    }

    pub(crate) fn schedule_transfer(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.transfer
            .schedule(self.data_host.clone(), &mut self.data_device, context)?;
        self.transfer.record_transferred(context)
    }
}
