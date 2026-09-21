//! GPU-owned host storage: the pinned allocator, the CUDA-registered guest RAM
//! and the pinned JIT trace chunk.

use crate::errors::GpuBackendError;
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

/// The pinned host allocator, wrapped so this crate can give it the shared
/// capacity contract: `HostTraceAllocator` (`execution_prover_model`) and
/// `ConcurrentStaticHostAllocator` (`gpu_core`) are both foreign here, so the
/// impl needs a local type.
#[derive(Clone, Debug, Default)]
pub struct GpuTraceAllocator(ConcurrentStaticHostAllocator);

impl GpuTraceAllocator {
    pub(crate) fn new(inner: ConcurrentStaticHostAllocator) -> Self {
        Self(inner)
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

/// Guest RAM registered with CUDA so the simulator's writes can be transferred
/// without a staging copy.
pub struct LockedBoxedMemoryHolder {
    pub holder: Box<MemoryHolder>,
}

impl LockedBoxedMemoryHolder {
    /// Registration pins a multi-gigabyte range and can fail, so the error is
    /// returned rather than unwrapped.
    pub fn try_new(ram_config: JitRunnerRam) -> Result<Self, GpuBackendError> {
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
            .map_err(|source| {
                GpuBackendError::cuda(
                    format!("CUDA registration of {total_size_bytes} bytes of guest RAM failed"),
                    source,
                )
            })?;
            Ok(Self { holder })
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

/// A JIT trace chunk in pinned host memory.
pub struct LockedBoxedTraceChunk {
    pub chunk: Box<TraceChunk, GpuTraceAllocator>,
}

impl LockedBoxedTraceChunk {
    pub fn try_new() -> Result<Self, GpuBackendError> {
        const LOG_CHUNK_SIZE: u32 = 20;
        let size = size_of::<TraceChunk>().next_multiple_of(1 << LOG_CHUNK_SIZE);
        let allocation =
            HostAllocation::alloc(size, CudaHostAllocFlags::DEFAULT).map_err(|source| {
                GpuBackendError::cuda(
                    format!("pinned host allocation of {size} bytes failed"),
                    source,
                )
            })?;
        let allocator = GpuTraceAllocator::new(ConcurrentStaticHostAllocator::new(
            [allocation],
            LOG_CHUNK_SIZE,
        ));
        // Zeroed rather than uninitialized: the JIT reads control fields
        // (`len`, the stop flag) before it writes them. `new_zeroed_in` writes
        // straight into the pinned allocation, so the multi-megabyte chunk is
        // never a stack temporary.
        // SAFETY: `TraceChunk` is plain data (`u32`/`u64` arrays and scalars),
        // so an all-zero bit pattern is a valid value.
        let chunk = unsafe { Box::<TraceChunk, _>::new_zeroed_in(allocator).assume_init() };
        Ok(Self { chunk })
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
