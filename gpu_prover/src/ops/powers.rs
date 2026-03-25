use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::field::*;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

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
get_powers_by_val_impl!(E6);

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
get_powers_by_ref_impl!(E6);

#[cfg(test)]
mod tests {
    use super::*;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::Field;

    fn assert_equal<T: PartialEq + core::fmt::Debug>((a, b): (T, T)) {
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

    #[test]
    fn get_powers_by_val_e6() {
        test_get_powers::<E6>(true);
    }

    #[test]
    fn get_powers_by_ref_e6() {
        test_get_powers::<E6>(false);
    }
}
