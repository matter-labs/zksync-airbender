use crate::allocator::host::ConcurrentStaticHostAllocator;
use era_cudart::memory::{CudaHostAllocFlags, HostAllocation as CudaHostAllocation};
use era_cudart::result::CudaResult;
use std::mem::size_of;

pub(crate) type StaticPinnedVec<T> = Vec<T, ConcurrentStaticHostAllocator>;

pub(crate) fn alloc_static_pinned_vec_uninit<T>(
    len: usize,
    log_chunk_size: u32,
) -> CudaResult<StaticPinnedVec<T>> {
    assert!(len > 0, "static pinned allocations must be non-empty");
    let bytes = len
        .checked_mul(size_of::<T>())
        .expect("static pinned allocation size overflow");
    assert!(
        bytes > 0,
        "zero-sized static pinned element types are unsupported"
    );
    let chunk_size = 1usize << log_chunk_size;
    let allocation_bytes = bytes.next_multiple_of(chunk_size);
    let allocation = CudaHostAllocation::alloc(allocation_bytes, CudaHostAllocFlags::DEFAULT)?;
    let allocator = ConcurrentStaticHostAllocator::new([allocation], log_chunk_size);
    let mut values = Vec::with_capacity_in(len, allocator);
    unsafe {
        values.set_len(len);
    }
    Ok(values)
}

pub(crate) fn alloc_static_pinned_vec_from_slice<T: Copy>(
    values: &[T],
    log_chunk_size: u32,
) -> CudaResult<StaticPinnedVec<T>> {
    let mut allocation = alloc_static_pinned_vec_uninit(values.len(), log_chunk_size)?;
    allocation.copy_from_slice(values);
    Ok(allocation)
}
