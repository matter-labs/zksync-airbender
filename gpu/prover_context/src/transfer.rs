use super::context::{ProverContext, H2D_STAGING_BYTES};
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use era_cudart::stream::CudaStreamWaitEventFlags;
use gpu_core::primitives::callbacks::Callbacks;
use std::mem::{self, MaybeUninit};
use std::ptr;
use std::sync::Arc;

struct StagedCopy {
    offset: usize,
    bytes: usize,
    dst: usize,
}

/// One bundle of H2D copies on `h2d_stream`, fenced against `exec_stream` by
/// the `allocated` and `transferred` events.
///
/// Small per-request values are recorded with [`Transfer::stage`] and packed
/// into the context's pinned staging buffer. The first allocation wait issues,
/// in order: one callback filling the staging buffer, the single wait for the
/// bundle's device allocations, and the staged copies. Each bundle's fill sits
/// behind every earlier staged copy on the in-order `h2d_stream`, so all
/// bundles reuse the one staging buffer.
pub struct Transfer<'a> {
    allocated: CudaEvent,
    transferred: CudaEvent,
    allocation_awaited: bool,
    staged_bytes: Vec<MaybeUninit<u8>>,
    staged_copies: Vec<StagedCopy>,
    callbacks: Callbacks<'a>,
    sources: Vec<Box<dyn Send + Sync + 'a>>,
}

/// H2D sources and the staging fill callback of a submitted [`Transfer`].
/// Keep it alive until stream or event synchronization confirms completion.
pub struct TransferKeepalive<'a> {
    _callbacks: Callbacks<'a>,
    _sources: Vec<Box<dyn Send + Sync + 'a>>,
}

impl<'a> Transfer<'a> {
    pub fn new() -> CudaResult<Self> {
        Ok(Self {
            allocated: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            transferred: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            allocation_awaited: false,
            staged_bytes: Vec::new(),
            staged_copies: Vec::new(),
            callbacks: Callbacks::new(),
            sources: Vec::new(),
        })
    }

    pub fn record_allocated(&self, context: &ProverContext) -> CudaResult<()> {
        self.allocated.record(context.get_exec_stream())
    }

    /// Orders `h2d_stream` after the bundle's device allocations. Only the
    /// first call issues work; it also submits everything staged so far.
    pub fn ensure_allocated(&mut self, context: &ProverContext) -> CudaResult<()> {
        if self.allocation_awaited {
            return Ok(());
        }
        self.allocation_awaited = true;
        let stream = context.get_h2d_stream();
        if !self.staged_copies.is_empty() {
            let staged_bytes = mem::take(&mut self.staged_bytes);
            let fill_target = context.h2d_staging_fill_target();
            self.callbacks.schedule(
                move || {
                    let target = unsafe { fill_target.get_mut() };
                    // SAFETY: `stage` bounds the packed bytes by the staging
                    // buffer size; this is an untyped copy between two
                    // distinct host allocations.
                    unsafe {
                        ptr::copy_nonoverlapping(
                            staged_bytes.as_ptr().cast::<u8>(),
                            target.as_mut_ptr(),
                            staged_bytes.len(),
                        )
                    };
                },
                stream,
            )?;
        }
        stream.wait_event(&self.allocated, CudaStreamWaitEventFlags::DEFAULT)?;
        let staging = context.h2d_staging_source();
        for StagedCopy { offset, bytes, dst } in mem::take(&mut self.staged_copies) {
            // SAFETY: `dst` came from a live `CudaSliceMut` of `bytes` bytes
            // owned by the bundle being scheduled.
            let dst = unsafe { DeviceSlice::from_raw_parts_mut(dst as *mut u8, bytes) };
            memory_copy_async(dst, &staging[offset..offset + bytes], stream)?;
        }
        Ok(())
    }

    /// Records a small H2D copy through the context's staging buffer. Stage
    /// every value before the bundle's first direct copy; `dst` must outlive
    /// the submission in [`Transfer::ensure_allocated`].
    pub fn stage<T: Copy>(&mut self, values: &[T], dst: &mut DeviceSlice<T>) {
        assert!(
            !self.allocation_awaited,
            "staged H2D recorded after the transfer was submitted"
        );
        assert_eq!(values.len(), dst.len());
        let offset = self.staged_bytes.len();
        let bytes = size_of_val(values);
        assert!(
            offset + bytes <= H2D_STAGING_BYTES,
            "{} staged H2D bytes exceed the {H2D_STAGING_BYTES}-byte staging buffer",
            offset + bytes
        );
        self.staged_bytes
            .resize(offset + bytes, MaybeUninit::uninit());
        // SAFETY: untyped copy of `bytes` bytes into the freshly sized tail.
        unsafe {
            ptr::copy_nonoverlapping(
                values.as_ptr().cast::<u8>(),
                self.staged_bytes[offset..].as_mut_ptr().cast::<u8>(),
                bytes,
            )
        };
        let dst = dst.as_mut_ptr() as usize;
        self.staged_copies.push(StagedCopy { offset, bytes, dst });
    }

    pub fn schedule<T>(
        &mut self,
        src: Arc<impl CudaSlice<T> + Send + Sync + ?Sized + 'a>,
        dst: &mut (impl CudaSliceMut<T> + ?Sized),
        context: &ProverContext,
    ) -> CudaResult<()> {
        assert_eq!(src.len(), dst.len());
        self.ensure_allocated(context)?;
        memory_copy_async(dst, src.as_ref(), context.get_h2d_stream())?;
        self.sources.push(Box::new(src));
        Ok(())
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
        self.sources.push(Box::new(srcs.to_vec()));
        Ok(())
    }

    pub fn record_transferred(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.ensure_allocated(context)?;
        self.transferred.record(context.get_h2d_stream())
    }

    pub fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        context
            .get_exec_stream()
            .wait_event(&self.transferred, CudaStreamWaitEventFlags::DEFAULT)
    }

    pub fn into_keepalive(self) -> TransferKeepalive<'a> {
        assert!(
            self.staged_copies.is_empty(),
            "staged H2D was never submitted"
        );
        TransferKeepalive {
            _callbacks: self.callbacks,
            _sources: self.sources,
        }
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
    use era_cudart::memory::memory_copy;
    use era_cudart::result::CudaResult;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use std::sync::Arc;

    #[test]
    fn test_transfer() -> CudaResult<()> {
        // 48 MB device arena (48 × default 1 MB blocks). Needs to be larger
        // than the two default `small_allocator_pool_blocks << block_log_size`
        // pools (2 × 16 × 1 MB) carved out of it; everything beyond that is
        // room for the 1 KB transfer this test actually exercises.
        let config = ProverContextConfig {
            device_allocation_blocks_count: Some(48),
            ..Default::default()
        };
        let context = ProverContext::new(&config)?;
        let src = Arc::new(vec![0; 1024]);
        let source_alive = Arc::downgrade(&src);
        let mut transfer = Transfer::new()?;
        let mut dst = context.alloc(1024, AllocationPlacement::BestFit)?;
        transfer.record_allocated(&context)?;
        transfer.schedule(src, &mut dst, &context)?;
        transfer.record_transferred(&context)?;
        let keepalive = transfer.into_keepalive();
        assert!(source_alive.upgrade().is_some());
        context.get_h2d_stream().synchronize()?;
        drop(keepalive);
        assert!(source_alive.upgrade().is_none());
        Ok(())
    }

    #[test]
    fn test_staged_transfers_share_staging() -> CudaResult<()> {
        let config = ProverContextConfig {
            device_allocation_blocks_count: Some(48),
            ..Default::default()
        };
        let context = ProverContext::new(&config)?;
        let direct = Arc::new((0..1024u32).rev().collect::<Vec<_>>());
        let mut bundles = Vec::new();
        for salt in [0u32, 0xdead_beef] {
            let words: Vec<u32> = (0..4096).map(|x| x ^ salt).collect();
            let bytes: Vec<u8> = (0..77).map(|x| x ^ salt as u8).collect();
            let mut words_dst = context.alloc(words.len(), AllocationPlacement::BestFit)?;
            let mut bytes_dst = context.alloc(bytes.len(), AllocationPlacement::BestFit)?;
            let mut direct_dst = context.alloc(direct.len(), AllocationPlacement::BestFit)?;
            let mut transfer = Transfer::new()?;
            transfer.record_allocated(&context)?;
            transfer.stage(&bytes, &mut bytes_dst);
            transfer.stage(&words, &mut words_dst);
            transfer.schedule(Arc::clone(&direct), &mut direct_dst, &context)?;
            transfer.record_transferred(&context)?;
            let keepalive = transfer.into_keepalive();
            bundles.push((words, words_dst, bytes, bytes_dst, direct_dst, keepalive));
        }
        context.get_h2d_stream().synchronize()?;
        for (words, words_dst, bytes, bytes_dst, direct_dst, _keepalive) in bundles {
            let mut words_host = vec![0u32; words.len()];
            memory_copy(&mut words_host, &words_dst)?;
            assert_eq!(words_host, words);
            let mut bytes_host = vec![0u8; bytes.len()];
            memory_copy(&mut bytes_host, &bytes_dst)?;
            assert_eq!(bytes_host, bytes);
            let mut direct_host = vec![0u32; direct.len()];
            memory_copy(&mut direct_host, &direct_dst)?;
            assert_eq!(&direct_host, direct.as_ref());
        }
        Ok(())
    }
}
