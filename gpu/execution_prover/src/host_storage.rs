use crate::A;
use era_cudart::memory::{CudaHostAllocFlags, CudaHostRegisterFlags, HostAllocation};
use era_cudart::result::CudaResultWrap;
use era_cudart_sys::{cudaHostRegister, cudaHostUnregister};
use execution_prover_model::allocator::HostTraceAllocator;
use fft::GoodAllocator;
use gpu_core::allocator::host::ConcurrentStaticHostAllocator;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::alloc::{AllocError, Allocator, Layout};
use std::ops::{Deref, DerefMut};
use std::os::raw::c_void;
use std::ptr::NonNull;

// A local type is required to implement the shared allocator trait for the GPU allocator.
#[derive(Clone, Debug, Default)]
pub struct GpuTraceAllocator(ConcurrentStaticHostAllocator);

impl GpuTraceAllocator {
    pub(crate) fn new(
        backends: impl IntoIterator<Item = HostAllocation<u8>>,
        log_chunk_size: u32,
    ) -> Self {
        Self(ConcurrentStaticHostAllocator::new(backends, log_chunk_size))
    }
}

unsafe impl Allocator for GpuTraceAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.0.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        self.0.deallocate(ptr, layout)
    }
}

impl GoodAllocator for GpuTraceAllocator {}

impl HostTraceAllocator for GpuTraceAllocator {
    fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

pub struct LockedBoxedMemoryHolder {
    pub holder: Box<MemoryHolder>,
}

impl LockedBoxedMemoryHolder {
    pub fn new(ram_config: JitRunnerRam) -> Self {
        // SAFETY: `MemoryHolder` is plain-data, so zero-init is sound; the boxed allocation
        // outlives the matching `cudaHostUnregister` call in `Drop`, keeping the pinned
        // registration valid for the holder's lifetime.
        unsafe {
            let mut holder = MemoryHolder::allocate_zeroed::<_>(ram_config, Default::default());
            let total_size_bytes = holder.byte_size();
            cudaHostRegister(
                holder.as_mut() as *mut MemoryHolder as *mut c_void,
                total_size_bytes,
                CudaHostRegisterFlags::DEFAULT.bits(),
            )
            .wrap()
            .unwrap();
            Self { holder }
        }
    }
}

impl Deref for LockedBoxedMemoryHolder {
    type Target = MemoryHolder;

    fn deref(&self) -> &Self::Target {
        &self.holder
    }
}

impl DerefMut for LockedBoxedMemoryHolder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.holder
    }
}

impl Drop for LockedBoxedMemoryHolder {
    fn drop(&mut self) {
        // SAFETY: mirrors the `cudaHostRegister` in `new`; the boxed holder is still alive.
        let result = unsafe {
            cudaHostUnregister(self.holder.as_mut() as *mut MemoryHolder as *mut c_void).wrap()
        };
        if std::thread::panicking() {
            if let Err(e) = result {
                log::error!("cudaHostUnregister failed during panic unwind: {e:?}");
            }
        } else {
            result.expect("cudaHostUnregister failed");
        }
    }
}

pub struct LockedBoxedTraceChunk {
    pub chunk: Box<TraceChunk, A>,
}

impl LockedBoxedTraceChunk {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        const LOG_CHUNK_SIZE: u32 = 20;
        let size = size_of::<TraceChunk>().next_multiple_of(1 << LOG_CHUNK_SIZE);
        let allocation = HostAllocation::alloc(size, CudaHostAllocFlags::DEFAULT).unwrap();
        let allocator = A::new([allocation], LOG_CHUNK_SIZE);
        // The JIT reads control fields before it writes them.
        // SAFETY: `TraceChunk` is plain data (`u32`/`u64` arrays and scalars),
        // so an all-zero bit pattern is a valid value.
        let chunk = unsafe { Box::<TraceChunk, _>::new_zeroed_in(allocator).assume_init() };
        Self { chunk }
    }
}

impl Deref for LockedBoxedTraceChunk {
    type Target = TraceChunk;

    fn deref(&self) -> &Self::Target {
        &self.chunk
    }
}

impl DerefMut for LockedBoxedTraceChunk {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.chunk
    }
}
