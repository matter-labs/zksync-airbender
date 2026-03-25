use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::field::*;
use crate::primitives::utils::{GetChunksCount, WARP_SIZE};

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
batch_inv_impl!(E6, 2);

#[cfg(test)]
mod tests {
    use super::*;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::{Field, Rand};
    use rand::rng;

    fn assert_equal<T: PartialEq + core::fmt::Debug>((a, b): (T, T)) {
        assert_eq!(a, b);
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
}
