use std::mem::size_of;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::*;
use gpu_core::primitives::utils::{get_grid_block_dims_for_warp_groups, LOG_WARP_SIZE, WARP_SIZE};

cuda_kernel_signature_arguments_and_function!(
    pub(crate) BitReverse<T>,
    src: PtrAndStride<T>,
    dst: MutPtrAndStride<T>,
    log_count: u32,
);

/// Internal per-size-class kernel binding. *Not* the public API — bit-reversal
/// is exposed through the size-generic [`bit_reverse_in_place`] free function.
/// One impl exists per supported element size (4/16/32 bytes), each binding the
/// matching `native/bit_reverse.cu` instantiation; `bit_reverse_in_place`
/// reinterprets any same-sized element type onto the right impl.
pub(crate) trait BitReverse: Sized {
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
            let (mut grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(1, 1 << log_count);
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

/// Bit-reverses the row order within each column of `values`, in place.
///
/// Generic over **any** element type `T`: bit-reversal permutes whole elements
/// and depends only on `size_of::<T>()`, so the element is reinterpreted as the
/// equal-sized kernel payload and dispatched to the matching kernel. Supported
/// element sizes are 4, 16, and 32 bytes (the instantiations in
/// `native/bit_reverse.cu`); any other size panics. Callers therefore need no
/// per-type `impl` — e.g. a blake2s digest (`[u32; 8]`, 32 bytes) and any other
/// 32-byte POD share the same path.
pub fn bit_reverse_in_place<T>(
    values: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let rows = values.rows();
    let cols = values.cols();
    let src = values.as_ptr_and_stride();
    let dst = values.as_mut_ptr_and_stride();
    match size_of::<T>() {
        4 => BF::launch(rows, cols, recast(src), recast_mut(dst), stream),
        16 => E4::launch(rows, cols, recast(src), recast_mut(dst), stream),
        32 => <[u32; 8]>::launch(rows, cols, recast(src), recast_mut(dst), stream),
        n => panic!(
            "bit_reverse_in_place: unsupported element size {n} bytes (supported: 4, 16, 32)"
        ),
    }
}

// Reinterpret a `PtrAndStride<T>` as an equal-sized kernel payload `B`.
//
// Bit-reversal copies whole elements and never inspects their contents, and the
// stride is expressed in elements (so column starts stay aligned for any
// integer stride once the base is aligned), so this is sound whenever
// `size_of::<T>() == size_of::<B>()` *and* the device base pointer meets the
// kernel payload's alignment.
//
// The native payloads (`bf`/`e4`/`dg`) are each aligned to their size (4/16/32
// bytes — `e4` is `__align__(16)`, `dg` is `__align__(32)`), and the kernels
// issue alignment-dependent vectorized loads/stores. A Rust element type may be
// less aligned than its size (e.g. `[u32; 8]` is `align 4`, size 32), so we
// assert the *runtime* device pointer is aligned to `size_of::<B>()` — passing
// an under-aligned buffer would be UB on the device.
#[inline]
fn align_check<B>(addr: usize, what: &str) {
    assert_eq!(
        addr % size_of::<B>(),
        0,
        "bit_reverse_in_place: {what} device pointer 0x{addr:x} is not {}-byte aligned, \
         as required by the {}-byte bit-reverse kernel",
        size_of::<B>(),
        size_of::<B>(),
    );
}

#[inline]
fn recast<T, B>(p: PtrAndStride<T>) -> PtrAndStride<B> {
    debug_assert_eq!(size_of::<T>(), size_of::<B>());
    align_check::<B>(p.ptr as usize, "source");
    PtrAndStride::new(p.ptr as *const B, p.stride)
}

#[inline]
fn recast_mut<T, B>(p: MutPtrAndStride<T>) -> MutPtrAndStride<B> {
    debug_assert_eq!(size_of::<T>(), size_of::<B>());
    align_check::<B>(p.ptr as usize, "destination");
    MutPtrAndStride::new(p.ptr as *mut B, p.stride)
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
bit_reverse_impl!(E4, BF);

// 32-byte size class. `[u32; 8]` is just the canonical 32-byte POD used to bind
// the kernel; `bit_reverse_in_place` routes *every* 32-byte element type here by
// reinterpretation, so this carries no digest vocabulary and downstream crates
// need no impl of their own. Kernel symbols come from `native/bit_reverse.cu`'s
// `BIT_REVERSE(dg, e4, 1)` / `BIT_REVERSE_NAIVE(dg)` instantiations (chunk `E4`).
cuda_kernel_declaration!(ab_bit_reverse_naive_dg_kernel(
    src: PtrAndStride<[u32; 8]>,
    dst: MutPtrAndStride<[u32; 8]>,
    log_count: u32,
));
cuda_kernel_declaration!(ab_bit_reverse_dg_kernel(
    src: PtrAndStride<E4>,
    dst: MutPtrAndStride<E4>,
    log_count: u32,
));
impl BitReverse for [u32; 8] {
    type ChunkType = E4;
    const NAIVE_KERNEL_FUNCTION: BitReverseSignature<Self> = ab_bit_reverse_naive_dg_kernel;
    const KERNEL_FUNCTION: BitReverseSignature<Self::ChunkType> = ab_bit_reverse_dg_kernel;
}

#[cfg(test)]
mod tests {
    use super::*;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::Rand;
    use gpu_core::primitives::device_structures::{
        DeviceMatrix, DeviceMatrixChunkImpl, DeviceMatrixMut,
    };
    use itertools::Itertools;
    use rand::rng;
    use serial_test::serial;

    pub(crate) fn bit_reverse<T: BitReverse>(
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

    impl BitReverseTest for E4 {
        fn rand(rng: &mut impl rand::Rng) -> Self {
            E4::random_element(rng)
        }
    }

    // 32-byte element path (the `[u32; 8]` impl; what `gpu_hash`'s digest uses).
    impl BitReverseTest for [u32; 8] {
        fn rand(rng: &mut impl rand::Rng) -> Self {
            std::array::from_fn(|_| BF::random_element(rng).0)
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
    #[serial]
    fn bit_reverse_bf() {
        test_bit_reverse::<BF>(false);
    }

    #[test]
    #[serial]
    fn bit_reverse_in_place_bf() {
        test_bit_reverse::<BF>(true);
    }

    #[test]
    #[serial]
    fn bit_reverse_b256() {
        test_bit_reverse::<[u32; 8]>(false);
    }

    #[test]
    #[serial]
    fn bit_reverse_in_place_b256() {
        test_bit_reverse::<[u32; 8]>(true);
    }

    #[test]
    #[serial]
    fn bit_reverse_e4() {
        test_bit_reverse::<E4>(false);
    }

    #[test]
    #[serial]
    fn bit_reverse_in_place_e4() {
        test_bit_reverse::<E4>(true);
    }

    /// Cross-check `bit_reverse_in_place::<E4>` against host
    /// `fft::bitreverse_enumeration_inplace` over a small E4 buffer. This is
    /// the device-resident replacement for the WHIR final-round
    /// `final_monomials` bitreverse callback; if the E4 instantiation diverges
    /// from the host helper, this test surfaces it before the WHIR smoke runs.
    #[test]
    #[serial]
    fn bit_reverse_e4_matches_host() {
        use fft::bitreverse_enumeration_inplace;
        const LOG_N: usize = 4;
        const N: usize = 1 << LOG_N;
        let mut rng = rng();
        let mut host: Vec<E4> = (0..N).map(|_| E4::random_element(&mut rng)).collect();
        let stream = CudaStream::default();
        let mut device = DeviceAllocation::<E4>::alloc(N).unwrap();
        memory_copy_async(&mut device, &host, &stream).unwrap();
        let mut matrix = DeviceMatrixMut::<E4>::new(&mut device, N);
        bit_reverse_in_place::<E4>(&mut matrix, &stream).unwrap();
        let mut device_back = vec![E4::default(); N];
        memory_copy_async(&mut device_back, &device, &stream).unwrap();
        stream.synchronize().unwrap();
        bitreverse_enumeration_inplace(&mut host);
        assert_eq!(host, device_back);
    }
}
