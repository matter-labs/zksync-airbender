use crate::allocator::{
    InnerStaticAllocatorWrapper, NonConcurrentInnerStaticAllocatorWrapper, StaticAllocation,
    StaticAllocationBackend, StaticAllocator,
};
use era_cudart::memory::DeviceAllocation;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub(crate) struct StaticDeviceAllocationBackend(pub(crate) DeviceAllocation<u8>);

impl Deref for StaticDeviceAllocationBackend {
    type Target = DeviceSlice<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for StaticDeviceAllocationBackend {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl StaticAllocationBackend for StaticDeviceAllocationBackend {
    fn as_non_null(&mut self) -> NonNull<u8> {
        // SAFETY: `DeviceAllocation::as_mut_ptr` returns a non-null device
        // pointer (cudaMalloc-backed; null would have failed allocation).
        unsafe { NonNull::new_unchecked(self.as_mut_ptr()) }
    }

    fn len(&self) -> usize {
        self.deref().len()
    }

    fn is_empty(&self) -> bool {
        self.deref().is_empty()
    }
}

trait InnerStaticDeviceAllocatorWrapper:
    InnerStaticAllocatorWrapper<StaticDeviceAllocationBackend>
{
}

type NonConcurrentInnerStaticDeviceAllocatorWrapper =
    NonConcurrentInnerStaticAllocatorWrapper<StaticDeviceAllocationBackend>;

impl InnerStaticDeviceAllocatorWrapper for NonConcurrentInnerStaticDeviceAllocatorWrapper {}

type StaticDeviceAllocator<W> = StaticAllocator<StaticDeviceAllocationBackend, W>;

type StaticDeviceAllocation<T, W> = StaticAllocation<T, StaticDeviceAllocationBackend, W>;

pub(crate) type NonConcurrentStaticDeviceAllocator =
    StaticDeviceAllocator<NonConcurrentInnerStaticDeviceAllocatorWrapper>;

pub(crate) type NonConcurrentStaticDeviceAllocation<T> =
    StaticDeviceAllocation<T, NonConcurrentInnerStaticDeviceAllocatorWrapper>;

impl<T, W: InnerStaticDeviceAllocatorWrapper> Deref for StaticDeviceAllocation<T, W> {
    type Target = DeviceSlice<T>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: `self.data.ptr` is a live `NonNull<T>` into the parent
        // `StaticDeviceAllocationBackend`, which outlives `self`; `self.data.len`
        // is the `T` count assigned at allocation. The allocator enforces `T`
        // alignment at `allocate` time.
        unsafe { DeviceSlice::from_raw_parts(self.data.ptr.as_ptr(), self.data.len) }
    }
}

impl<T, W: InnerStaticDeviceAllocatorWrapper> DerefMut for StaticDeviceAllocation<T, W> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: as in `deref`, plus the `&mut self` receiver provides
        // exclusive access to this allocation's slot in the parent backend.
        unsafe { DeviceSlice::from_raw_parts_mut(self.data.ptr.as_ptr(), self.data.len) }
    }
}

impl<T, W: InnerStaticDeviceAllocatorWrapper> CudaSlice<T> for StaticDeviceAllocation<T, W> {
    unsafe fn as_slice(&self) -> &[T] {
        DeviceSlice::<T>::as_slice(self)
    }
}

impl<T, W: InnerStaticDeviceAllocatorWrapper> CudaSliceMut<T> for StaticDeviceAllocation<T, W> {
    unsafe fn as_mut_slice(&mut self) -> &mut [T] {
        DeviceSlice::<T>::as_mut_slice(self)
    }
}
