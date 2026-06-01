use crate::allocator::device::{
    NonConcurrentStaticDeviceAllocation, NonConcurrentStaticDeviceAllocator,
};
use crate::allocator::host::{ConcurrentStaticHostAllocator, NonConcurrentStaticHostAllocator};
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut};
use era_cudart_sys::CudaDeviceAttr;

pub type DeviceAllocator = NonConcurrentStaticDeviceAllocator;
pub type DeviceAllocation<T> = NonConcurrentStaticDeviceAllocation<T>;
pub type HostAllocator = NonConcurrentStaticHostAllocator;
pub type SchedulerHostAllocator = ConcurrentStaticHostAllocator;

pub struct DeviceProperties {
    pub l2_cache_size_bytes: usize,
    pub sm_count: usize,
    pub compute_capability_major: usize,
    pub compute_capability_minor: usize,
}

impl DeviceProperties {
    pub fn new() -> CudaResult<Self> {
        let device_id = get_device()?;
        let l2_cache_size_bytes =
            device_get_attribute(CudaDeviceAttr::L2CacheSize, device_id)? as usize;
        let sm_count =
            device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)? as usize;
        let compute_capability_major =
            device_get_attribute(CudaDeviceAttr::ComputeCapabilityMajor, device_id)? as usize;
        let compute_capability_minor =
            device_get_attribute(CudaDeviceAttr::ComputeCapabilityMinor, device_id)? as usize;
        Ok(Self {
            l2_cache_size_bytes,
            sm_count,
            compute_capability_major,
            compute_capability_minor,
        })
    }
}

/// Raw `*const T` wrapper that escapes Rust borrow-checking so a captured
/// reference can travel into a stream-scheduled host callback.
///
/// Only the holder's lifetime is enforced — at call sites the pointee must
/// still outlive every dereference. See
/// [`docs/gpu_scheduling_contract.md`](../../docs/gpu_scheduling_contract.md)
/// for the lifetime and access rules.
#[repr(transparent)]
pub struct UnsafeAccessor<T: ?Sized>(*const T);

impl<T: ?Sized> UnsafeAccessor<T> {
    pub fn new(value: &T) -> Self {
        UnsafeAccessor(value as *const T)
    }

    /// # Safety
    ///
    /// May only be called from inside a stream-scheduled host callback
    /// (`Callbacks::schedule` / `launch_host_fn`) whose ordering establishes
    /// that the referent has been initialized by prior stream ops and is not
    /// being concurrently mutated. The original holder must remain alive
    /// until that callback has been *scheduled*; see contract doc.
    pub unsafe fn get(&self) -> &T {
        &*self.0
    }
}

impl<T: ?Sized> Clone for UnsafeAccessor<T> {
    fn clone(&self) -> Self {
        UnsafeAccessor(self.0)
    }
}

impl<T: ?Sized> Copy for UnsafeAccessor<T> {}

// SAFETY: `UnsafeAccessor<T>` is a raw pointer wrapper used to thread a
// borrow into a stream-scheduled callback running on a different thread.
// The scheduling contract (see `docs/gpu_scheduling_contract.md`) makes the
// caller responsible for ordering reads/writes; the type itself adds no new
// thread-safety obligations beyond `Sync`/`Send` of `*const T`.
unsafe impl<T: ?Sized> Send for UnsafeAccessor<T> {}
unsafe impl<T: ?Sized> Sync for UnsafeAccessor<T> {}

/// Raw `*mut T` wrapper with the same intent as [`UnsafeAccessor`] but for
/// mutable borrows.
///
/// See [`docs/gpu_scheduling_contract.md`](../../docs/gpu_scheduling_contract.md)
/// for the write-exclusivity and lifetime rules.
#[repr(transparent)]
pub struct UnsafeMutAccessor<T: ?Sized>(*mut T);

impl<T: ?Sized> UnsafeMutAccessor<T> {
    pub fn new(value: &mut T) -> Self {
        UnsafeMutAccessor(value as *mut T)
    }

    /// # Safety
    ///
    /// May only be called from inside a stream-scheduled host callback whose
    /// ordering guarantees the referent has been initialized and is not being
    /// concurrently mutated by another stream op. See contract doc.
    pub unsafe fn get(&self) -> &T {
        &*self.0
    }

    /// # Safety
    ///
    /// Only valid inside a stream-scheduled host callback. Write-exclusivity
    /// is enforced by scheduling order, not by the type: at most one stream
    /// op (callback or kernel) may write the referent at a time, per the
    /// fork/join window rules in `docs/gpu_scheduling_contract.md`.
    pub unsafe fn get_mut(&self) -> &mut T {
        &mut *(self.0)
    }
}

impl<T: ?Sized> Clone for UnsafeMutAccessor<T> {
    fn clone(&self) -> Self {
        UnsafeMutAccessor(self.0)
    }
}

impl<T: ?Sized> Copy for UnsafeMutAccessor<T> {}

// SAFETY: see `UnsafeAccessor` Send/Sync note above; the scheduling contract
// governs write-exclusivity and lifetime.
unsafe impl<T: ?Sized> Send for UnsafeMutAccessor<T> {}
unsafe impl<T: ?Sized> Sync for UnsafeMutAccessor<T> {}

pub struct HostAllocation<T: ?Sized>(Box<T, HostAllocator>);

impl<T: ?Sized> HostAllocation<T> {
    pub fn get_accessor(&self) -> UnsafeAccessor<T> {
        UnsafeAccessor::new(&self.0)
    }

    pub fn get_mut_accessor(&mut self) -> UnsafeMutAccessor<T> {
        UnsafeMutAccessor::new(&mut self.0)
    }
}

impl<T> HostAllocation<[T]> {
    pub unsafe fn new_uninit_slice_in(len: usize, allocator: HostAllocator) -> Self {
        Self(Box::new_uninit_slice_in(len, allocator).assume_init())
    }
}

impl<T> CudaSlice<T> for HostAllocation<T> {
    unsafe fn as_slice(&self) -> &[T] {
        std::slice::from_ref(&self.0)
    }
}

impl<T> CudaSliceMut<T> for HostAllocation<T> {
    unsafe fn as_mut_slice(&mut self) -> &mut [T] {
        std::slice::from_mut(&mut self.0)
    }
}

impl<T> CudaSlice<T> for HostAllocation<[T]> {
    unsafe fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<T> CudaSliceMut<T> for HostAllocation<[T]> {
    unsafe fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
}
