use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::static_host::StaticPinnedBox;
use crate::prover::transfer::Transfer;
use crate::prover::ProverContext;
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use era_cudart::result::CudaResult;
use std::marker::PhantomData;
use std::sync::Arc;

pub struct DecoderTableTransfer<'a> {
    pub(crate) data_host: Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>,
    pub(crate) data_device: DeviceAllocation<ExecutorFamilyDecoderData>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> DecoderTableTransfer<'a> {
    pub fn new(
        data_host: Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let data_device = context.alloc(data_host.len(), AllocationPlacement::Bottom)?;
        Ok(Self {
            data_host,
            data_device,
            _marker: PhantomData,
        })
    }

    pub(crate) fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.schedule(self.data_host.clone(), &mut self.data_device, context)
    }
}
