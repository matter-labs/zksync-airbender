use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::static_host::StaticPinnedBox;
use crate::primitives::transfer::Transfer;
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use era_cudart::result::CudaResult;
use std::sync::Arc;

pub(crate) struct DecoderTableTransfer<'a> {
    pub(crate) data_host: Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>,
    pub(crate) data_device: DeviceAllocation<ExecutorFamilyDecoderData>,
    pub(crate) transfer: Transfer<'a>,
}

impl<'a> DecoderTableTransfer<'a> {
    pub(crate) fn new(
        data_host: Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>,
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

    pub(crate) fn into_host_keepalive(self) -> crate::primitives::callbacks::Callbacks<'a> {
        let Self {
            data_host: _,
            data_device: _,
            transfer,
        } = self;
        transfer.into_callbacks()
    }
}
