use super::context::ProverContext;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use era_cudart::stream::CudaStreamWaitEventFlags;
use gpu_core::primitives::callbacks::Callbacks;
use std::sync::Arc;

pub struct Transfer<'a> {
    pub(crate) allocated: CudaEvent,
    pub(crate) transferred: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
}

impl<'a> Transfer<'a> {
    pub fn new() -> CudaResult<Self> {
        Ok(Self {
            allocated: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            transferred: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            callbacks: Callbacks::new(),
        })
    }

    pub fn record_allocated(&self, context: &ProverContext) -> CudaResult<()> {
        self.allocated.record(context.get_exec_stream())
    }

    pub fn ensure_allocated(&self, context: &ProverContext) -> CudaResult<()> {
        context
            .get_h2d_stream()
            .wait_event(&self.allocated, CudaStreamWaitEventFlags::DEFAULT)
    }

    // Ownership moves into the callback that keeps the H2D source alive.
    #[allow(clippy::needless_pass_by_value)]
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
            // SAFETY: `dst` is a `CudaSliceMut` chunk, the sub-slice is in-bounds by the
            // preceding `assert_eq!` on total length, and the chunk lives for the H2D copy.
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

    pub fn record_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transferred.record(context.get_h2d_stream())
    }

    pub fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        context
            .get_exec_stream()
            .wait_event(&self.transferred, CudaStreamWaitEventFlags::DEFAULT)
    }

    pub fn into_callbacks(self) -> Callbacks<'a> {
        self.callbacks
    }
}

/// Test helper that schedules and records a complete one-shot H2D transfer.
/// Callers must wait for it before consuming the device buffers.
#[doc(hidden)]
pub fn single_shot_h2d<'a, F>(f: F, context: &ProverContext) -> CudaResult<Transfer<'a>>
where
    F: FnOnce(&mut Transfer<'a>) -> CudaResult<()>,
{
    let mut transfer = Transfer::new()?;
    transfer.record_allocated(context)?;
    f(&mut transfer)?;
    transfer.record_transferred(context)?;
    Ok(transfer)
}

#[cfg(test)]
mod tests {
    use super::super::{ProverContext, ProverContextConfig};
    use super::Transfer;
    use era_cudart::result::CudaResult;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use std::sync::Arc;

    #[test]
    fn test_transfer() -> CudaResult<()> {
        // 32 MB device arena (32 × default 1 MB blocks). Needs to be larger
        // than the default `small_allocator_pool_blocks << block_log_size`
        // (16 × 1 MB) carved out of it; everything beyond that is room for
        // the 1 KB transfer this test actually exercises.
        let config = ProverContextConfig {
            max_device_allocation_blocks_count: Some(32),
            ..Default::default()
        };
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
