use std::mem::size_of;

use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};

use crate::blake2s::Digest;
use crate::device_context::CIRCLE_GROUP_LOG_ORDER;
use crate::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::field::{BaseField, Ext2Field, Ext4Field};
use crate::utils::{
    get_grid_block_dims_for_threads_count, GetChunksCount, LOG_WARP_SIZE, WARP_SIZE,
};

type BF = BaseField;
type E2 = Ext2Field;
type E4 = Ext4Field;
type DG = Digest;

fn get_launch_dims(count: u32) -> (Dim3, Dim3) {
    get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count)
}

cuda_kernel_signature_arguments_and_function!(
    GetPowersByVal<T>,
    base: T,
    offset: u32,
    bit_reverse: bool,
    result: *mut T,
    count: u32,
);

macro_rules! get_powers_by_val_kernel {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_get_powers_by_val_ $type:lower _kernel>](
                    base: $type,
                    offset: u32,
                    bit_reverse: bool,
                    result: *mut $type,
                    count: u32,
                )
            );
        }
    };
}

pub trait GetPowersByVal: Sized {
    const KERNEL_FUNCTION: GetPowersByValSignature<Self>;
}

pub fn get_powers_by_val<T: GetPowersByVal>(
    base: T,
    offset: u32,
    bit_reverse: bool,
    result: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(result.len() <= u32::MAX as usize);
    let count = result.len() as u32;
    let (grid_dim, block_dim) = get_launch_dims(count);
    let result = result.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GetPowersByValArguments::new(base, offset, bit_reverse, result, count);
    GetPowersByValFunction(T::KERNEL_FUNCTION).launch(&config, &args)
}

macro_rules! get_powers_by_val_impl {
    ($type:ty) => {
        paste! {
            get_powers_by_val_kernel!($type);
            impl GetPowersByVal for $type {
                const KERNEL_FUNCTION: GetPowersByValSignature<Self> = [<ab_get_powers_by_val_ $type:lower _kernel>];
            }
        }
    };
}

get_powers_by_val_impl!(BF);
get_powers_by_val_impl!(E2);
get_powers_by_val_impl!(E4);

cuda_kernel_signature_arguments_and_function!(
    GetPowersByRef<T>,
    base: *const T,
    offset: u32,
    bit_reverse: bool,
    result: *mut T,
    count: u32,
);

macro_rules! get_powers_by_ref_kernel {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_get_powers_by_ref_ $type:lower _kernel>](
                    base: *const $type,
                    offset: u32,
                    bit_reverse: bool,
                    result: *mut $type,
                    count: u32,
                )
            );
        }
    };
}

pub trait GetPowersByRef: Sized {
    const KERNEL_FUNCTION: GetPowersByRefSignature<Self>;
}

pub fn get_powers_by_ref<T: GetPowersByRef>(
    base: &DeviceVariable<T>,
    offset: u32,
    bit_reverse: bool,
    result: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(result.len() <= u32::MAX as usize);
    let count = result.len() as u32;
    let (grid_dim, block_dim) = get_launch_dims(count);
    let base = base.as_ptr();
    let result = result.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GetPowersByRefArguments::new(base, offset, bit_reverse, result, count);
    GetPowersByRefFunction(T::KERNEL_FUNCTION).launch(&config, &args)
}

macro_rules! get_powers_by_ref_impl {
    ($type:ty) => {
        paste! {
            get_powers_by_ref_kernel!($type);
            impl GetPowersByRef for $type {
                const KERNEL_FUNCTION: GetPowersByRefSignature<Self> = [<ab_get_powers_by_ref_ $type:lower _kernel>];
            }
        }
    };
}

get_powers_by_ref_impl!(BF);
get_powers_by_ref_impl!(E2);
get_powers_by_ref_impl!(E4);

cuda_kernel_signature_arguments_and_function!(
    BatchInv<T>,
    src: *const T,
    dst: *mut T,
    count: u32,
);

macro_rules! batch_inv_kernel {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_batch_inv_ $type:lower _kernel>](
                    src: *const $type,
                    dst: *mut $type,
                    count: u32,
                )
            );
        }
    };
}

pub trait BatchInv {
    const BATCH_SIZE: u32;
    const KERNEL_FUNCTION: BatchInvSignature<Self>;
}

pub fn launch_batch_inv<T: BatchInv>(
    src: *const T,
    dst: *mut T,
    count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let block_dim = WARP_SIZE * 4;
    let grid_dim = count.get_chunks_count(T::BATCH_SIZE * block_dim);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = BatchInvArguments::<T>::new(src, dst, count);
    BatchInvFunction::<T>(T::KERNEL_FUNCTION).launch(&config, &args)
}

pub fn batch_inv<T: BatchInv>(
    src: &DeviceSlice<T>,
    dst: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src.len(), dst.len());
    assert!(dst.len() <= u32::MAX as usize);
    launch_batch_inv::<T>(src.as_ptr(), dst.as_mut_ptr(), dst.len() as u32, stream)
}

pub fn batch_inv_in_place<T: BatchInv>(
    values: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(values.len() <= u32::MAX as usize);
    launch_batch_inv::<T>(
        values.as_ptr(),
        values.as_mut_ptr(),
        values.len() as u32,
        stream,
    )
}

macro_rules! batch_inv_impl {
    ($type:ty, $batch_size:expr) => {
        paste! {
            batch_inv_kernel!($type);
            impl BatchInv for $type {
                const BATCH_SIZE: u32 = $batch_size;
                const KERNEL_FUNCTION: BatchInvSignature<Self> = [<ab_batch_inv_ $type:lower _kernel>];
            }
        }
    };
}

batch_inv_impl!(BF, 20);
batch_inv_impl!(E2, 5);
batch_inv_impl!(E4, 3);

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

cuda_kernel!(
    Fold,
    ab_fold_kernel(
        challenge: *const E4,
        src: *const E4,
        dst: *mut E4,
        root_shift: u32,
        log_count: u32,
    )
);

pub fn fold(
    challenge: &DeviceVariable<E4>,
    src: &DeviceSlice<E4>,
    dst: &mut DeviceSlice<E4>,
    root_offset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(src.len().is_power_of_two());
    assert!(dst.len().is_power_of_two());
    let log_count = dst.len().trailing_zeros();
    assert_eq!(src.len().trailing_zeros(), log_count + 1);
    assert!(log_count < 32);
    assert!(root_offset + (1 << log_count) < (1 << CIRCLE_GROUP_LOG_ORDER));
    let root_offset = root_offset as u32;
    let (grid_dim, block_dim) = get_launch_dims(1 << log_count);
    let challenge = challenge.as_ptr();
    let src = src.as_ptr();
    let dst = dst.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = FoldArguments::new(challenge, src, dst, root_offset, log_count);
    FoldFunction::default().launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use std::alloc::Global;
    use std::fmt::Debug;

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use fft::precompute_twiddles_for_fft;
    use field::Rand;
    use field::{Field, FieldExtension};
    use itertools::Itertools;
    use rand::rng;
    use serial_test::serial;
    use worker::Worker;

    use crate::device_context::DeviceContext;
    use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};

    use super::*;

    type BF = BaseField;
    type E2 = Ext2Field;
    type E4 = Ext4Field;

    fn assert_equal<T: PartialEq + Debug>((a, b): (T, T)) {
        assert_eq!(a, b);
    }

    fn test_get_powers<F: GetPowersByVal + GetPowersByRef + Field>(by_val: bool) {
        const N: usize = 1 << 16;
        let mut h_result = vec![F::ZERO; N];
        let mut d_result = DeviceAllocation::alloc(N).unwrap();
        let stream = CudaStream::default();
        let mut base = F::ONE;
        base.add_assign(&F::ONE);
        let mut d_base = DeviceAllocation::alloc(1).unwrap();
        memory_copy_async(&mut d_base, &[base], &stream).unwrap();
        let b = &d_base[0];
        let (d_result_0, d_result_1) = d_result.split_at_mut(N / 2);
        if by_val {
            get_powers_by_val(base, 0, false, d_result_0, &stream).unwrap();
            get_powers_by_val(base, N as u32 / 2, false, d_result_1, &stream).unwrap();
        } else {
            get_powers_by_ref(b, 0, false, d_result_0, &stream).unwrap();
            get_powers_by_ref(b, N as u32 / 2, false, d_result_1, &stream).unwrap();
        }
        memory_copy_async(&mut h_result, &d_result, &stream).unwrap();
        stream.synchronize().unwrap();
        h_result
            .into_iter()
            .enumerate()
            .map(|(i, x)| (base.pow(i as u32), x))
            .for_each(assert_equal);
    }

    #[test]
    fn get_powers_by_val_bf() {
        test_get_powers::<BF>(true);
    }

    #[test]
    fn get_powers_by_ref_bf() {
        test_get_powers::<BF>(false);
    }

    #[test]
    fn get_powers_by_val_e2() {
        test_get_powers::<E2>(true);
    }

    #[test]
    fn get_powers_by_ref_e2() {
        test_get_powers::<E2>(false);
    }

    #[test]
    fn get_powers_by_val_e4() {
        test_get_powers::<E4>(true);
    }

    #[test]
    fn get_powers_by_ref_e4() {
        test_get_powers::<E4>(false);
    }

    fn test_batch_inv<F: BatchInv + Field + Rand>(in_place: bool) {
        const LOG_N: usize = 16;
        const N: usize = 1 << LOG_N;
        let mut rng = rng();
        let h_src: Vec<F> = (0..N).map(|_| F::random_element(&mut rng)).collect();
        let mut h_dst = vec![F::ONE; N];
        let stream = CudaStream::default();
        if in_place {
            let mut d_values = DeviceAllocation::alloc(N).unwrap();
            memory_copy_async(&mut d_values, &h_src, &stream).unwrap();
            batch_inv_in_place::<F>(&mut d_values, &stream).unwrap();
            memory_copy_async(&mut h_dst, &d_values, &stream).unwrap();
        } else {
            let mut d_src = DeviceAllocation::alloc(N).unwrap();
            let mut d_dst = DeviceAllocation::alloc(N).unwrap();
            memory_copy_async(&mut d_src, &h_src, &stream).unwrap();
            batch_inv::<F>(&d_src, &mut d_dst, &stream).unwrap();
            memory_copy_async(&mut h_dst, &d_dst, &stream).unwrap();
        }
        stream.synchronize().unwrap();
        h_src
            .into_iter()
            .map(|x| x.inverse().unwrap_or_default())
            .zip(h_dst)
            .for_each(assert_equal);
    }

    #[test]
    fn batch_inv_bf() {
        test_batch_inv::<BF>(false);
    }

    #[test]
    fn batch_inv_bf_in_place() {
        test_batch_inv::<BF>(true);
    }

    #[test]
    fn batch_inv_e2() {
        test_batch_inv::<E2>(false);
    }

    #[test]
    fn batch_inv_e2_in_place() {
        test_batch_inv::<E2>(true);
    }

    fn test_transpose<T: Transpose + Default + Copy + Clone + Debug + Eq + Rand>() -> CudaResult<()>
    {
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

    trait BitReverseTest: BitReverse + Default + Copy + Clone + Debug + Eq {
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

    #[test]
    #[serial]
    fn fold() {
        const LOG_N: u32 = 16;
        const N: usize = 1 << LOG_N;
        const ROOT_OFFSET: usize = N;
        let context = DeviceContext::create(12).unwrap();
        let worker = Worker::new_with_num_threads(1);
        let roots = precompute_twiddles_for_fft::<E2, Global, true>(N * 4, &worker);
        let mut rng = rng();
        let h_challenge = [E4::random_element(&mut rng)];
        let h_src = (0..N * 2)
            .map(|_| E4::random_element(&mut rng))
            .collect_vec();
        let mut h_dst = vec![E4::ZERO; N];
        let stream = CudaStream::default();
        let mut d_challenge = DeviceAllocation::alloc(1).unwrap();
        let mut d_src = DeviceAllocation::alloc(N * 2).unwrap();
        let mut d_dst = DeviceAllocation::alloc(N).unwrap();
        memory_copy_async(&mut d_challenge, &h_challenge, &stream).unwrap();
        memory_copy_async(&mut d_src, &h_src, &stream).unwrap();
        super::fold(&d_challenge[0], &d_src, &mut d_dst, ROOT_OFFSET, &stream).unwrap();
        memory_copy_async(&mut h_dst, &d_dst, &stream).unwrap();
        stream.synchronize().unwrap();
        context.destroy().unwrap();
        h_src
            .into_iter()
            .chunks(2)
            .into_iter()
            .enumerate()
            .map(|(i, mut chunk)| {
                let even = chunk.next().unwrap();
                let odd = chunk.next().unwrap();
                let mut sum = even;
                sum.add_assign(&odd);
                let mut diff = even;
                diff.sub_assign(&odd);
                diff.mul_assign_by_base(&roots[i + ROOT_OFFSET]);
                diff.mul_assign(&h_challenge[0]);
                sum.add_assign(&diff);
                sum
            })
            .zip(h_dst)
            .for_each(assert_equal);
    }
}
