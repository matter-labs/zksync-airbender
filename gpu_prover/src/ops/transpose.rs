use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::*;
use crate::primitives::utils::{GetChunksCount, LOG_WARP_SIZE};

cuda_kernel_signature_arguments_and_function!(
    Transpose<T>,
    src: PtrAndStride<T>,
    dst: MutPtrAndStride<T>,
    src_rows: u32,
    src_cols: u32,
);

macro_rules! transpose_kernel {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_transpose_ $type:lower _kernel>](
                    src: PtrAndStride<$type>,
                    dst: MutPtrAndStride<$type>,
                    src_rows: u32,
                    src_cols: u32,
                )
            );
        }
    };
}

pub trait Transpose: Sized {
    const LOG_TILE_SIZE: u32;
    const KERNEL_FUNCTION: TransposeSignature<Self>;

    fn launch(
        src: &(impl DeviceMatrixChunkImpl<Self> + ?Sized),
        dst: &mut (impl DeviceMatrixChunkMutImpl<Self> + ?Sized),
        stream: &CudaStream,
    ) -> CudaResult<()> {
        const LOG_BLOCK_SIZE: u32 = LOG_WARP_SIZE + 2;
        let log_tiles_per_block = LOG_BLOCK_SIZE - Self::LOG_TILE_SIZE;
        let tile_size = 1 << Self::LOG_TILE_SIZE;
        let tiles_per_block = 1 << log_tiles_per_block;
        let src_rows = src.rows();
        let src_cols = src.cols();
        assert_eq!(src_rows, dst.cols());
        assert_eq!(src_cols, dst.rows());
        let src_rows = src_rows as u32;
        let src_cols = src_cols as u32;
        let block_dim = (tile_size, tiles_per_block);
        let tile_rows = src_rows.get_chunks_count(tile_size);
        let tile_cols = src_cols.get_chunks_count(tile_size);
        let tiles = tile_rows * tile_cols;
        let grid_dim = tiles.get_chunks_count(tiles_per_block);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let src = src.as_ptr_and_stride();
        let dst = dst.as_mut_ptr_and_stride();
        let args = TransposeArguments::<Self>::new(src, dst, src_rows, src_cols);
        TransposeFunction(Self::KERNEL_FUNCTION).launch(&config, &args)
    }
}

pub fn transpose<T: Transpose>(
    src: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
    dst: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    T::launch(src, dst, stream)
}

macro_rules! transpose_impl {
    ($type:ty, $log_tile_size:expr) => {
        paste! {
            transpose_kernel!($type);
            impl Transpose for $type {
                const LOG_TILE_SIZE: u32 = $log_tile_size;
                const KERNEL_FUNCTION: TransposeSignature<Self> = [<ab_transpose_ $type:lower _kernel>];
            }
        }
    };
}

transpose_impl!(BF, 5);
transpose_impl!(E2, 4);
transpose_impl!(E4, 3);
transpose_impl!(E6, 3);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::Rand;
    use itertools::Itertools;
    use rand::rng;

    fn test_transpose<T: Transpose + Default + Copy + Clone + core::fmt::Debug + Eq + Rand>(
    ) -> CudaResult<()> {
        const ROWS: usize = 12345;
        const COLS: usize = 123;
        const N: usize = COLS * ROWS;
        let h_src = (0..N).map(|_| T::random_element(&mut rng())).collect_vec();
        let mut d_src = DeviceAllocation::alloc(N)?;
        let mut h_dst = vec![T::default(); N];
        let mut d_dst = DeviceAllocation::alloc(N)?;
        let stream = CudaStream::default();
        memory_copy_async(&mut d_src, &h_src, &stream)?;
        transpose(
            &DeviceMatrix::new(&d_src, ROWS),
            &mut DeviceMatrixMut::new(&mut d_dst, COLS),
            &stream,
        )?;
        memory_copy_async(&mut h_dst, &d_dst, &stream)?;
        stream.synchronize()?;
        for i in 0..COLS {
            for j in 0..ROWS {
                assert_eq!(
                    h_src[i * ROWS + j],
                    h_dst[j * COLS + i],
                    "i = {}, j = {}",
                    i,
                    j
                );
            }
        }
        Ok(())
    }

    #[test]
    fn transpose_bf() {
        test_transpose::<BF>().unwrap();
    }

    #[test]
    fn transpose_e2() {
        test_transpose::<E2>().unwrap();
    }

    #[test]
    fn transpose_e4() {
        test_transpose::<E4>().unwrap();
    }

    #[test]
    fn transpose_e6() {
        test_transpose::<E6>().unwrap();
    }
}
