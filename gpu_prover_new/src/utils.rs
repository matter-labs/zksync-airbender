use std::cmp::min;
use std::mem::size_of;
use std::os::raw::c_void;

use era_cudart::execution::Dim3;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaMemcpyToSymbol, cudaMemcpyToSymbolAsync, CudaMemoryCopyKind};

pub const LOG_WARP_SIZE: u32 = 5;
pub const WARP_SIZE: u32 = 1 << LOG_WARP_SIZE;

pub trait GetChunksCount {
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

pub fn get_grid_block_dims_for_threads_count(
    threads_per_block: u32,
    threads_count: u32,
) -> (Dim3, Dim3) {
    let block_dim = min(threads_count, threads_per_block);
    let grid_dim = threads_count.get_chunks_count(block_dim);
    (grid_dim.into(), block_dim.into())
}

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

#[allow(clippy::missing_safety_doc)]
pub unsafe fn memcpy_to_symbol_async<T>(
    symbol: &T,
    src: &T,
    stream: &CudaStream,
) -> CudaResult<()> {
    cudaMemcpyToSymbolAsync(
        symbol as *const T as *const c_void,
        src as *const T as *const c_void,
        size_of::<T>(),
        0,
        CudaMemoryCopyKind::HostToDevice,
        stream.into(),
    )
    .wrap()
}

// #[inline(always)]
// #[allow(dead_code)]
// pub fn bitreverse_index(n: usize, l: usize) -> usize {
//     if l == 0 {
//         assert_eq!(n, 0);
//         return 0;
//     }
//     let r = n.reverse_bits();
//     // now we need to only use the bits that originally were "last" l, so shift
//     r >> (size_of::<usize>() * 8) - l
// }
