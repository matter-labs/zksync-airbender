use crate::allocator::{
    ConcurrentInnerStaticAllocatorWrapper, InnerStaticAllocatorWrapper,
    NonConcurrentInnerStaticAllocatorWrapper, StaticAllocation, StaticAllocationBackend,
    StaticAllocator,
};
use era_cudart::memory::DeviceAllocation;
use era_cudart::memory_pools::DevicePoolAllocation;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub enum StaticDeviceAllocationBackend {
    DeviceAllocation(DeviceAllocation<u8>),
    DevicePoolAllocation(DevicePoolAllocation<'static, u8>),
}

impl Deref for StaticDeviceAllocationBackend {
    type Target = DeviceSlice<u8>;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::DeviceAllocation(allocation) => allocation,
            Self::DevicePoolAllocation(allocation) => allocation,
        }
    }
}

impl DerefMut for StaticDeviceAllocationBackend {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::DeviceAllocation(allocation) => allocation,
            Self::DevicePoolAllocation(allocation) => allocation,
        }
    }
}

impl StaticAllocationBackend for StaticDeviceAllocationBackend {
    fn as_non_null(&mut self) -> NonNull<u8> {
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

type ConcurrentInnerStaticDeviceAllocatorWrapper =
    ConcurrentInnerStaticAllocatorWrapper<StaticDeviceAllocationBackend>;

impl InnerStaticDeviceAllocatorWrapper for ConcurrentInnerStaticDeviceAllocatorWrapper {}

type NonConcurrentInnerStaticDeviceAllocatorWrapper =
    NonConcurrentInnerStaticAllocatorWrapper<StaticDeviceAllocationBackend>;

impl InnerStaticDeviceAllocatorWrapper for NonConcurrentInnerStaticDeviceAllocatorWrapper {}

type StaticDeviceAllocator<W> = StaticAllocator<StaticDeviceAllocationBackend, W>;

type StaticDeviceAllocation<T, W> = StaticAllocation<T, StaticDeviceAllocationBackend, W>;

pub type ConcurrentStaticDeviceAllocator =
    StaticDeviceAllocator<ConcurrentInnerStaticDeviceAllocatorWrapper>;

pub type ConcurrentStaticDeviceAllocation<T> =
    StaticDeviceAllocation<T, ConcurrentInnerStaticDeviceAllocatorWrapper>;

pub type NonConcurrentStaticDeviceAllocator =
    StaticDeviceAllocator<NonConcurrentInnerStaticDeviceAllocatorWrapper>;

pub type NonConcurrentStaticDeviceAllocation<T> =
    StaticDeviceAllocation<T, NonConcurrentInnerStaticDeviceAllocatorWrapper>;

impl<T, W: InnerStaticDeviceAllocatorWrapper> Deref for StaticDeviceAllocation<T, W> {
    type Target = DeviceSlice<T>;

    fn deref(&self) -> &Self::Target {
        unsafe { DeviceSlice::from_raw_parts(self.data.ptr.as_ptr(), self.data.len) }
    }
}

impl<T, W: InnerStaticDeviceAllocatorWrapper> DerefMut for StaticDeviceAllocation<T, W> {
    fn deref_mut(&mut self) -> &mut Self::Target {
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
