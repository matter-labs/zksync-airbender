use std::cmp::min;
use std::mem::size_of;
use std::os::raw::c_void;

use era_cudart::execution::Dim3;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::{cudaMemcpyToSymbol, CudaMemoryCopyKind};

pub(crate) const LOG_WARP_SIZE: u32 = 5;
pub(crate) const WARP_SIZE: u32 = 1 << LOG_WARP_SIZE;

pub(crate) trait GetChunksCount {
    fn get_chunks_count(self, chunk_size: Self) -> Self;
}

impl GetChunksCount for u32 {
    fn get_chunks_count(self, chunk_size: Self) -> Self {
        self.next_multiple_of(chunk_size) / chunk_size
    }
}

impl GetChunksCount for usize {
    fn get_chunks_count(self, chunk_size: Self) -> Self {
        self.next_multiple_of(chunk_size) / chunk_size
    }
}

pub(crate) fn get_grid_block_dims_for_threads_count(
    threads_per_block: u32,
    threads_count: u32,
) -> (Dim3, Dim3) {
    let block_dim = min(threads_count, threads_per_block);
    let grid_dim = threads_count.get_chunks_count(block_dim);
    (grid_dim.into(), block_dim.into())
}

pub(crate) fn get_grid_block_dims_for_warp_groups(
    warps_per_block: u32,
    threads_count: u32,
) -> (Dim3, Dim3) {
    get_grid_block_dims_for_threads_count(WARP_SIZE * warps_per_block, threads_count)
}

#[allow(clippy::missing_safety_doc)]
pub(crate) unsafe fn memcpy_to_symbol<T>(symbol: &T, src: &T) -> CudaResult<()> {
    cudaMemcpyToSymbol(
        symbol as *const T as *const c_void,
        src as *const T as *const c_void,
        size_of::<T>(),
        0,
        CudaMemoryCopyKind::HostToDevice,
    )
    .wrap()
}

// ---------------------------------------------------------------------------
// Shared-memory carveout helpers
// ---------------------------------------------------------------------------

/// Query the configurable shared-memory / L1 pool size (bytes) for the current device.
pub(crate) fn smem_pool_bytes_per_sm() -> usize {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart_sys::CudaDeviceAttr;
    let device_id = get_device().expect("get_device failed");
    device_get_attribute(CudaDeviceAttr::MaxSharedMemoryPerMultiprocessor, device_id)
        .expect("query MaxSharedMemoryPerMultiprocessor failed") as usize
}

/// Compute the smallest carveout percentage that accommodates a kernel's
/// static shared memory at maximum occupancy.
pub(crate) fn compute_minimal_carveout(
    kernel: *const c_void,
    block_size: i32,
    pool_bytes: usize,
) -> i32 {
    use era_cudart_sys::{
        cudaFuncGetAttributes, cudaOccupancyMaxActiveBlocksPerMultiprocessor, CudaFuncAttributes,
    };
    let mut attrs = std::mem::MaybeUninit::<CudaFuncAttributes>::zeroed();
    // SAFETY: attrs is a plain-data struct; kernel pointer is valid (points to a __global__ fn).
    unsafe { cudaFuncGetAttributes(attrs.as_mut_ptr(), kernel) }
        .wrap()
        .expect("cudaFuncGetAttributes failed");
    let smem_per_block = unsafe { attrs.assume_init() }.sharedSizeBytes;
    if smem_per_block == 0 {
        return 0;
    }

    let mut max_blocks: i32 = 0;
    // SAFETY: max_blocks is a valid i32 pointer; kernel and block_size are valid.
    unsafe {
        cudaOccupancyMaxActiveBlocksPerMultiprocessor(
            &mut max_blocks,
            kernel,
            block_size,
            0, // no dynamic shared memory
        )
    }
    .wrap()
    .expect("cudaOccupancyMaxActiveBlocksPerMultiprocessor failed");

    let total_smem = smem_per_block * max_blocks as usize;
    // Round up to the next whole percent.
    ((total_smem * 100 + pool_bytes - 1) / pool_bytes) as i32
}

/// Set the preferred shared-memory carveout percentage for a kernel.
pub(crate) fn set_shared_carveout(kernel: *const c_void, pct: i32) {
    use era_cudart_sys::CudaFuncAttribute;
    unsafe {
        era_cudart_sys::cudaFuncSetAttribute(
            kernel,
            CudaFuncAttribute::PreferredSharedMemoryCarveout,
            pct,
        )
    }
    .wrap()
    .unwrap_or_else(|e| {
        panic!("cudaFuncSetAttribute(PreferredSharedMemoryCarveout, {pct}) failed: {e:?}")
    });
}
