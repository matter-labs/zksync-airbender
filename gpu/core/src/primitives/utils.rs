use std::cmp::min;
use std::mem::size_of;
use std::os::raw::c_void;

use era_cudart::execution::Dim3;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::{cudaMemcpyToSymbol, CudaMemoryCopyKind};

pub const LOG_WARP_SIZE: u32 = 5;
pub const WARP_SIZE: u32 = 1 << LOG_WARP_SIZE;

pub trait GetChunksCount {
    fn get_chunks_count(self, chunk_size: Self) -> Self;
}

impl GetChunksCount for u32 {
    fn get_chunks_count(self, chunk_size: Self) -> Self {
        self.div_ceil(chunk_size)
    }
}

impl GetChunksCount for usize {
    fn get_chunks_count(self, chunk_size: Self) -> Self {
        self.div_ceil(chunk_size)
    }
}

pub fn get_grid_block_dims_for_threads_count(
    threads_per_block: u32,
    threads_count: u32,
) -> (Dim3, Dim3) {
    let block_dim = min(threads_count, threads_per_block);
    let grid_dim = threads_count.get_chunks_count(block_dim);
    (grid_dim.into(), block_dim.into())
}

pub fn get_grid_block_dims_for_warp_groups(
    warps_per_block: u32,
    threads_count: u32,
) -> (Dim3, Dim3) {
    get_grid_block_dims_for_threads_count(WARP_SIZE * warps_per_block, threads_count)
}

/// A pointer-typed `__device__ __constant__` symbol (`const T*` device-side), for
/// use as the type in a [`era_cudart_sys::cuda_struct_and_stub`] declaration.
///
/// `repr(transparent)`, so the symbol layout stays exactly `*const T`. It exists to
/// carry the `Sync` impl below: in `no_cuda` mode `cuda_struct_and_stub!` lowers a
/// symbol to a real `static`, which must be `Sync`, and a bare `*const T` is neither
/// `Sync` nor able to be given the impl locally (orphan rule).
#[repr(transparent)]
pub struct ConstPtrSymbol<T>(pub *const T);

// SAFETY: the wrapped value is a device address. It is never dereferenced on the
// host — the symbol is only ever addressed (`&symbol`) or memcpy'd to the device by
// `memcpy_to_symbol` — so sharing one across threads carries no aliasing risk.
unsafe impl<T> Sync for ConstPtrSymbol<T> {}

#[allow(clippy::missing_safety_doc)]
pub unsafe fn memcpy_to_symbol<T>(symbol: &T, src: &T) -> CudaResult<()> {
    cudaMemcpyToSymbol(
        symbol as *const T as *const c_void,
        src as *const T as *const c_void,
        size_of::<T>(),
        0,
        CudaMemoryCopyKind::HostToDevice,
    )
    .wrap()
}
