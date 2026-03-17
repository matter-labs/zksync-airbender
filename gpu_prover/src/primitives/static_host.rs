use crate::allocator::host::ConcurrentStaticHostAllocator;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation as CudaHostAllocation};
use era_cudart::result::CudaResult;
use std::mem::size_of;

pub(crate) type StaticPinnedBox<T> = Box<[T], ConcurrentStaticHostAllocator>;

pub(crate) fn alloc_static_pinned_box_uninit<T>(len: usize) -> CudaResult<StaticPinnedBox<T>> {
    assert!(len > 0, "static pinned allocations must be non-empty");
    let bytes = len
        .checked_mul(size_of::<T>())
        .expect("static pinned allocation size overflow");
    assert!(
        bytes > 0,
        "zero-sized static pinned element types are unsupported"
    );
    let allocation = CudaHostAllocation::alloc(bytes, CudaHostAllocFlags::DEFAULT)?;
    // These boxed slices own a dedicated pinned allocation each, so they do not need chunked
    // reuse. Use 1-byte chunks to make the allocator's bookkeeping match the exact byte size.
    let allocator = ConcurrentStaticHostAllocator::new([allocation], 0);
    // SAFETY: the boxed slice is backed by a fresh pinned allocation sized exactly for `len`
    // elements of `T`, and callers initialize every element before reading it.
    unsafe { Ok(Box::<[T], _>::new_uninit_slice_in(len, allocator).assume_init()) }
}

pub(crate) fn alloc_static_pinned_box_from_slice<T: Copy>(
    values: &[T],
) -> CudaResult<StaticPinnedBox<T>> {
    let mut allocation = alloc_static_pinned_box_uninit(values.len())?;
    allocation.copy_from_slice(values);
    Ok(allocation)
}
