use std::mem::size_of;

use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::ops::blake2s::DG;
use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::*;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, LOG_WARP_SIZE, WARP_SIZE};

fn get_launch_dims(count: u32) -> (Dim3, Dim3) {
    get_grid_block_dims_for_threads_count(WARP_SIZE, count)
}

cuda_kernel_signature_arguments_and_function!(
    BitReverse<T>,
    src: PtrAndStride<T>,
    dst: MutPtrAndStride<T>,
    log_count: u32,
);

pub trait BitReverse: Sized {
    type ChunkType: Sized;
    const NAIVE_KERNEL_FUNCTION: BitReverseSignature<Self>;
    const KERNEL_FUNCTION: BitReverseSignature<Self::ChunkType>;

    fn launch(
        rows: usize,
        cols: usize,
        src: PtrAndStride<Self>,
        dst: MutPtrAndStride<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        assert!(rows.is_power_of_two());
        assert!(rows <= u32::MAX as usize);
        assert!(cols <= u32::MAX as usize);
        let log_count = rows.trailing_zeros();
        let half_log_count = log_count >> 1;
        assert_eq!(size_of::<Self>() % size_of::<Self::ChunkType>(), 0);
        let chunk_size = size_of::<Self>() / size_of::<Self::ChunkType>();
        assert!(chunk_size.is_power_of_two());
        let log_chunk_size = chunk_size.trailing_zeros();
        assert!(log_chunk_size <= LOG_WARP_SIZE);
        let log_tile_dim = LOG_WARP_SIZE - log_chunk_size;
        if half_log_count <= log_tile_dim {
            let (mut grid_dim, block_dim) = get_launch_dims(1 << log_count);
            grid_dim.y = cols as u32;
            let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            let args = BitReverseArguments::<Self>::new(src, dst, log_count);
            BitReverseFunction(Self::NAIVE_KERNEL_FUNCTION).launch(&config, &args)
        } else {
            assert!(half_log_count > log_tile_dim);
            const BLOCK_ROWS: u32 = 2;
            let tiles_per_dim = 1 << (half_log_count - log_tile_dim);
            let grid_dim_x = tiles_per_dim * (tiles_per_dim + 1) / 2;
            let grid_dim_y = log_count - (half_log_count << 1) + 1;
            let grid_dim_z = cols as u32;
            let grid_dim = (grid_dim_x, grid_dim_y, grid_dim_z);
            let block_dim = (WARP_SIZE, BLOCK_ROWS, 2);
            let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            let src = PtrAndStride::new(
                src.ptr as *const Self::ChunkType,
                src.stride << log_chunk_size,
            );
            let dst = MutPtrAndStride::new(
                dst.ptr as *mut Self::ChunkType,
                dst.stride << log_chunk_size,
            );
            let args = BitReverseArguments::new(src, dst, log_count);
            BitReverseFunction(Self::KERNEL_FUNCTION).launch(&config, &args)
        }
    }
}

pub fn bit_reverse<T: BitReverse>(
    src: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
    dst: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let rows = dst.rows();
    let cols = dst.cols();
    assert_eq!(src.rows(), rows);
    assert_eq!(src.cols(), cols);
    let src = src.as_ptr_and_stride();
    let dst = dst.as_mut_ptr_and_stride();
    T::launch(rows, cols, src, dst, stream)
}

pub fn bit_reverse_in_place<T: BitReverse>(
    values: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let rows = values.rows();
    let cols = values.cols();
    let src = values.as_ptr_and_stride();
    let dst = values.as_mut_ptr_and_stride();
    T::launch(rows, cols, src, dst, stream)
}

macro_rules! bit_reverse_kernels {
    ($type:ty, $chunk_type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_bit_reverse_naive_ $type:lower _kernel>](
                    src: PtrAndStride<$type>,
                    dst: MutPtrAndStride<$type>,
                    log_count: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_bit_reverse_ $type:lower _kernel>](
                    src: PtrAndStride<$chunk_type>,
                    dst: MutPtrAndStride<$chunk_type>,
                    log_count: u32,
                )
            );
        }
    };
}

macro_rules! bit_reverse_impl {
    ($type:ty, $chunk_type:ty) => {
        paste! {
            bit_reverse_kernels!($type, $chunk_type);
            impl BitReverse for $type {
                type ChunkType = $chunk_type;
                const NAIVE_KERNEL_FUNCTION: BitReverseSignature<Self> = [<ab_bit_reverse_naive_ $type:lower _kernel>];
                const KERNEL_FUNCTION: BitReverseSignature<Self::ChunkType> = [<ab_bit_reverse_ $type:lower _kernel>];
            }
        }
    };
}

bit_reverse_impl!(BF, BF);
bit_reverse_impl!(E2, E2);
bit_reverse_impl!(E4, E4);
bit_reverse_impl!(DG, E4);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::blake2s::DG;
    use crate::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::Rand;
    use itertools::Itertools;
    use rand::rng;

    fn assert_equal<T: PartialEq + core::fmt::Debug>((a, b): (T, T)) {
        assert_eq!(a, b);
    }

    trait BitReverseTest: BitReverse + Default + Copy + Clone + core::fmt::Debug + Eq {
        fn rand(rng: &mut impl rand::Rng) -> Self;
    }

    impl BitReverseTest for BF {
        fn rand(rng: &mut impl rand::Rng) -> Self {
            Self::random_element(rng)
        }
    }

    impl BitReverseTest for E2 {
        fn rand(rng: &mut impl rand::Rng) -> Self {
            Self::random_element(rng)
        }
    }

    impl BitReverseTest for E4 {
        fn rand(rng: &mut impl rand::Rng) -> Self {
            Self::random_element(rng)
        }
    }

    impl BitReverseTest for DG {
        fn rand(rng: &mut impl rand::Rng) -> Self {
            let mut result = Self::default();
            result.fill_with(|| BF::random_element(rng).0);
            result
        }
    }

    fn test_bit_reverse<T: BitReverseTest>(in_place: bool) {
        const LOG_ROWS: usize = 16;
        const ROWS: usize = 1 << LOG_ROWS;
        const COLS: usize = 16;
        const N: usize = COLS << LOG_ROWS;
        let h_src = (0..N).map(|_| T::rand(&mut rng())).collect_vec();
        let mut h_dst = vec![T::default(); N];
        let stream = CudaStream::default();
        if in_place {
            let mut d_values = DeviceAllocation::alloc(N).unwrap();
            memory_copy_async(&mut d_values, &h_src, &stream).unwrap();
            let mut matrix = DeviceMatrixMut::new(&mut d_values, ROWS);
            bit_reverse_in_place(&mut matrix, &stream).unwrap();
            memory_copy_async(&mut h_dst, &d_values, &stream).unwrap();
        } else {
            let mut d_src = DeviceAllocation::alloc(N).unwrap();
            let mut d_dst = DeviceAllocation::alloc(N).unwrap();
            memory_copy_async(&mut d_src, &h_src, &stream).unwrap();
            let src_matrix = DeviceMatrix::new(&d_src, ROWS);
            let mut dst_matrix = DeviceMatrixMut::new(&mut d_dst, ROWS);
            bit_reverse(&src_matrix, &mut dst_matrix, &stream).unwrap();
            memory_copy_async(&mut h_dst, &d_dst, &stream).unwrap();
        }
        stream.synchronize().unwrap();
        h_src
            .into_iter()
            .chunks(ROWS)
            .into_iter()
            .zip(h_dst.chunks(ROWS))
            .for_each(|(s, d)| {
                s.enumerate()
                    .map(|(i, x)| (x, d[i.reverse_bits() >> (usize::BITS - LOG_ROWS as u32)]))
                    .for_each(assert_equal);
            });
    }

    #[test]
    fn bit_reverse_bf() {
        test_bit_reverse::<BF>(false);
    }

    #[test]
    fn bit_reverse_in_place_bf() {
        test_bit_reverse::<BF>(true);
    }

    #[test]
    fn bit_reverse_e2() {
        test_bit_reverse::<E2>(false);
    }

    #[test]
    fn bit_reverse_in_place_e2() {
        test_bit_reverse::<E2>(true);
    }

    #[test]
    fn bit_reverse_e4() {
        test_bit_reverse::<E4>(false);
    }

    #[test]
    fn bit_reverse_in_place_e4() {
        test_bit_reverse::<E4>(true);
    }

    #[test]
    fn bit_reverse_dg() {
        test_bit_reverse::<DG>(false);
    }

    #[test]
    fn bit_reverse_in_place_dg() {
        test_bit_reverse::<DG>(true);
    }
}
