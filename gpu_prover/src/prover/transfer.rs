use crate::prover::callbacks::Callbacks;
use crate::prover::context::ProverContext;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut};
use era_cudart::stream::CudaStreamWaitEventFlags;
use std::ops::Deref;
use std::sync::{Arc, Mutex};

pub struct Transfer<'a> {
    pub(crate) allocated: CudaEvent,
    pub(crate) transferred: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
}

impl<'a> Transfer<'a> {
    pub(crate) fn new() -> CudaResult<Self> {
        Ok(Self {
            allocated: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            transferred: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            callbacks: Callbacks::new(),
        })
    }

    pub(crate) fn record_allocated(&self, context: &ProverContext) -> CudaResult<()> {
        self.allocated.record(context.get_exec_stream())
    }

    pub(crate) fn ensure_allocated(&self, context: &ProverContext) -> CudaResult<()> {
        context
            .get_h2d_stream()
            .wait_event(&self.allocated, CudaStreamWaitEventFlags::DEFAULT)
    }

    pub fn schedule<T>(
        &mut self,
        src: Arc<impl CudaSlice<T> + Send + Sync + ?Sized + 'a>,
        dst: &mut (impl CudaSliceMut<T> + ?Sized),
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(src.len(), dst.len());
        self.ensure_allocated(context)?;
        let stream = context.get_h2d_stream();
        memory_copy_async(dst, src.deref(), stream)?;
        let src = Mutex::new(Some(src));
        let f = move || {
            src.lock().unwrap().take();
        };
        self.callbacks.schedule(f, stream)
    }

    pub(crate) fn record_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transferred.record(context.get_h2d_stream())
    }

    pub fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        context
            .get_exec_stream()
            .wait_event(&self.transferred, CudaStreamWaitEventFlags::DEFAULT)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::tracker::AllocationPlacement;
    use crate::prover::context::ProverContextConfig;

    #[test]
    fn test_transfer() -> CudaResult<()> {
        let context = ProverContext::new(&ProverContextConfig::default())?;
        let src = Arc::new(vec![0; 1024]);
        let mut transfer = Transfer::new()?;
        let mut dst = context.alloc(1024, AllocationPlacement::BestFit)?;
        transfer.record_allocated(&context)?;
        transfer.schedule(src, &mut dst, &context)?;
        transfer.record_transferred(&context)?;
        Ok(())
    }
}
