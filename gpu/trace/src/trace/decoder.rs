use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use std::marker::PhantomData;
use std::sync::Arc;

pub struct DecoderTableTransfer<'a> {
    pub(crate) data_host: Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>,
    // pub: apex production (`prover::gkr::setup`) reads the device table across the split.
    pub data_device: DeviceAllocation<ExecutorFamilyDecoderData>,
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

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.schedule(self.data_host.clone(), &mut self.data_device, context)
    }
}
