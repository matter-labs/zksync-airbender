use super::callbacks::Callbacks;
use super::context::ProverContext;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use era_cudart::stream::{CudaStream, CudaStreamWaitEventFlags};
use std::sync::Arc;

/// One-shot exec → d2h fork/join wrapper. Records a `DISABLE_TIMING` event
/// on `exec_stream`, waits on it from `d2h_stream`, runs `body` with the
/// d2h stream, then joins via the symmetric event back to `exec_stream`.
///
/// Use for per-layer D2H bundles where every source has been written on
/// exec by the time of the fork and exec needs the D2Hs visible before
/// proceeding (e.g., before scheduling a final-readback callback or
/// dropping the source allocations).
pub(crate) fn fork_join_exec_to_d2h<R, F>(
    exec_stream: &CudaStream,
    d2h_stream: &CudaStream,
    body: F,
) -> CudaResult<R>
where
    F: FnOnce(&CudaStream) -> CudaResult<R>,
{
    let src_ready = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    src_ready.record(exec_stream)?;
    d2h_stream.wait_event(&src_ready, CudaStreamWaitEventFlags::DEFAULT)?;

    let result = body(d2h_stream)?;

    let d2h_done = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    d2h_done.record(d2h_stream)?;
    exec_stream.wait_event(&d2h_done, CudaStreamWaitEventFlags::DEFAULT)?;
    Ok(result)
}

pub(crate) struct Transfer<'a> {
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
        memory_copy_async(dst, src.as_ref(), stream)?;
        let src = src.clone();
        let f = move || {
            let _ = src;
        };
        self.callbacks.schedule(f, stream)
    }

    pub fn schedule_multiple<T>(
        &mut self,
        srcs: &[Arc<impl CudaSlice<T> + Send + Sync + ?Sized + 'a>],
        dst: &mut (impl CudaSliceMut<T> + ?Sized),
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(srcs.iter().map(|s| s.len()).sum::<usize>(), dst.len());
        self.ensure_allocated(context)?;
        let stream = context.get_h2d_stream();
        let mut offset = 0;
        for src in srcs.iter() {
            let dst = unsafe {
                let slice = &mut dst.as_mut_slice()[offset..offset + src.len()];
                DeviceSlice::from_mut_slice(slice)
            };
            memory_copy_async(dst, src.as_ref(), stream)?;
            offset += src.len();
        }
        let srcs = srcs.to_vec();
        let f = move || {
            let _ = srcs;
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

    pub(crate) fn into_callbacks(self) -> Callbacks<'a> {
        self.callbacks
    }
}

#[cfg(test)]
mod tests {
    use super::super::context::{ProverContext, ProverContextConfig};
    use super::Transfer;
    use crate::allocator::tracker::AllocationPlacement;
    use era_cudart::result::CudaResult;
    use std::sync::Arc;

    #[test]
    fn test_transfer() -> CudaResult<()> {
        let mut config = ProverContextConfig::default();
        config.allocator_block_log_size = 2;
        let context = ProverContext::new(&config)?;
        let src = Arc::new(vec![0; 1024]);
        let mut transfer = Transfer::new()?;
        let mut dst = context.alloc(1024, AllocationPlacement::BestFit)?;
        transfer.record_allocated(&context)?;
        transfer.schedule(src, &mut dst, &context)?;
        transfer.record_transferred(&context)?;
        Ok(())
    }
}
