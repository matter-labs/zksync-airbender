use super::context::ProverContext;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use era_cudart::stream::{CudaStream, CudaStreamWaitEventFlags};
use gpu_core::primitives::callbacks::Callbacks;
use std::sync::Arc;

/// One-shot exec → d2h fork/join wrapper. Records a `DISABLE_TIMING` event
/// on `exec_stream`, waits on it from `d2h_stream`, runs `body` with the
/// d2h stream, then joins via the symmetric event back to `exec_stream`.
///
/// Use for per-layer D2H bundles where every source has been written on
/// exec by the time of the fork and exec needs the D2Hs visible before
/// proceeding (e.g., before scheduling a final-readback callback or
/// dropping the source allocations).
///
/// `pub` (not `pub(crate)`): production code in `gpu_circuit_prover`'s
/// `gkr::backward` module schedules D2H fork/join bundles through this helper
/// across the crate boundary.
pub fn fork_join_exec_to_d2h<R, F>(
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

// `#[doc(hidden)] pub` (not `pub(crate)`) so `gpu_circuit_prover`'s test suites can
// reach this type across the crate boundary. // test-reference readers
#[doc(hidden)]
pub struct Transfer<'a> {
    pub(crate) allocated: CudaEvent,
    pub(crate) transferred: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
}

impl<'a> Transfer<'a> {
    // `pub` (not `pub(crate)`): production code in `gpu_circuit_prover`'s
    // `trace::memory_transfer` constructs and drives a `Transfer` directly
    // across the crate boundary (not just via `single_shot_h2d`).
    pub fn new() -> CudaResult<Self> {
        Ok(Self {
            allocated: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            transferred: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            callbacks: Callbacks::new(),
        })
    }

    // `pub` (not `pub(crate)`): production code in `gpu_circuit_prover`'s
    // `trace::memory_transfer` records a `Transfer`'s allocation event
    // directly across the crate boundary.
    pub fn record_allocated(&self, context: &ProverContext) -> CudaResult<()> {
        self.allocated.record(context.get_exec_stream())
    }

    // `pub` (not `pub(crate)`): production code in `gpu_circuit_prover`'s
    // `trace::memory_transfer` waits on a `Transfer`'s allocation event
    // directly across the crate boundary.
    pub fn ensure_allocated(&self, context: &ProverContext) -> CudaResult<()> {
        context
            .get_h2d_stream()
            .wait_event(&self.allocated, CudaStreamWaitEventFlags::DEFAULT)
    }

    // `needless_pass_by_value`: clippy's `&Arc` + internal-clone suggestion is
    // equivalent, but by-value keeps the ownership transfer explicit at every
    // `schedule` call site across the `gpu_trace`/`gpu_circuit_prover`
    // boundary (the callback below moves `src` directly instead of an extra
    // clone-then-move, so this is not a wasted allocation either way).
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
        // `src` is already owned here, so move it into the callback directly
        // instead of cloning: the callback's only job is to keep the H2D
        // source alive until the copy completes.
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

    // `pub` (not `pub(crate)`): production code in `gpu_circuit_prover`'s
    // `trace::memory_transfer` records a `Transfer`'s transferred event
    // directly across the crate boundary.
    pub fn record_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transferred.record(context.get_h2d_stream())
    }

    pub fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        context
            .get_exec_stream()
            .wait_event(&self.transferred, CudaStreamWaitEventFlags::DEFAULT)
    }

    // `pub` (not `pub(crate)`): production code in `gpu_circuit_prover`'s
    // `trace::memory_transfer` and `proof::inputs` unwraps a finished
    // `Transfer` into its `Callbacks` directly across the crate boundary.
    pub fn into_callbacks(self) -> Callbacks<'a> {
        self.callbacks
    }
}

/// Test-only convenience for running a single wrapper's `schedule_transfer`
/// through its own one-shot `Transfer`, e.g.
/// `single_shot_h2d(|t| wrapper.schedule_transfer(t, context), context)?`.
///
/// The returned `Transfer` has its `transferred` event already recorded; the
/// caller should either `ensure_transferred` on it or `h2d_stream.synchronize()`
/// before consuming the device buffers.
// `#[doc(hidden)] pub` (not `#[cfg(test)]`) so `gpu_circuit_prover`'s test suites can
// reach this helper across the crate boundary. // test-reference readers
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
