use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::memory::memory_set_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStrideWrappingMatrix,
    PtrAndStrideWrappingMatrix,
};
use gpu_core::primitives::field::{BF, E2, E4, E6};
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

pub fn set_to_zero<T>(result: &mut DeviceSlice<T>, stream: &CudaStream) -> CudaResult<()> {
    memory_set_async(unsafe { result.transmute_mut() }, 0, stream)
}

pub fn set_to_ones<T>(result: &mut DeviceSlice<T>, stream: &CudaStream) -> CudaResult<()> {
    memory_set_async(unsafe { result.transmute_mut() }, 0xFF, stream)
}

fn get_launch_dims(rows: u32, cols: u32) -> (Dim3, Dim3) {
    let (mut grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, rows);
    grid_dim.y = cols;
    (grid_dim, block_dim)
}

// SET_BY_VAL_KERNEL
cuda_kernel_signature_arguments_and_function!(
    SetByVal<T>,
    value: T,
    result: MutPtrAndStrideWrappingMatrix<T>,
);

macro_rules! set_by_val_kernel {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_set_by_val_ $type:lower _kernel>](
                    value: $type,
                    result: MutPtrAndStrideWrappingMatrix<$type>,
                )
            );
        }
    };
}

pub trait SetByVal: Sized {
    const KERNEL_FUNCTION: SetByValSignature<Self>;
}

pub fn set_by_val<T: SetByVal>(
    value: T,
    result: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let result = MutPtrAndStrideWrappingMatrix::new(result);
    let (grid_dim, block_dim) = get_launch_dims(result.rows, result.cols);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = SetByValArguments::new(value, result);
    SetByValFunction(T::KERNEL_FUNCTION).launch(&config, &args)
}

macro_rules! set_by_val_impl {
    ($type:ty) => {
        paste! {
            set_by_val_kernel!($type);
            impl SetByVal for $type {
                const KERNEL_FUNCTION: SetByValSignature<Self> = [<ab_set_by_val_ $type:lower _kernel>];
            }
        }
    };
}

set_by_val_impl!(u32);
set_by_val_impl!(u64);
set_by_val_impl!(BF);
set_by_val_impl!(E2);
set_by_val_impl!(E4);
set_by_val_impl!(E6);

// SET_BY_REF_KERNEL
cuda_kernel_signature_arguments_and_function!(
    SetByRef<T>,
    values: PtrAndStrideWrappingMatrix<T>,
    result: MutPtrAndStrideWrappingMatrix<T>,
);

macro_rules! set_by_ref_kernel {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_set_by_ref_ $type:lower _kernel>](
                    values: PtrAndStrideWrappingMatrix<$type>,
                    result: MutPtrAndStrideWrappingMatrix<$type>,
                )
            );
        }
    };
}

pub trait SetByRef: Sized {
    const KERNEL_FUNCTION: SetByRefSignature<Self>;
}

// `#[doc(hidden)] pub` (not `#[cfg(test)]`) so `gpu_circuit_prover`'s test suites can
// reach this helper across the crate boundary.
#[doc(hidden)]
pub fn set_by_ref<T: SetByRef>(
    values: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
    result: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let values = PtrAndStrideWrappingMatrix::new(values);
    let result = MutPtrAndStrideWrappingMatrix::new(result);
    let (grid_dim, block_dim) = get_launch_dims(result.rows, result.cols);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = SetByRefArguments::<T>::new(values, result);
    SetByRefFunction::<T>(T::KERNEL_FUNCTION).launch(&config, &args)
}

macro_rules! set_by_ref_impl {
    ($type:ty) => {
        paste! {
            set_by_ref_kernel!($type);
            impl SetByRef for $type {
                const KERNEL_FUNCTION: SetByRefSignature<Self> = [<ab_set_by_ref_ $type:lower _kernel>];
            }
        }
    };
}

set_by_ref_impl!(u32);
set_by_ref_impl!(u64);
set_by_ref_impl!(BF);
set_by_ref_impl!(E2);
set_by_ref_impl!(E4);
set_by_ref_impl!(E6);

// PARAMETRIZED_KERNEL
cuda_kernel_signature_arguments_and_function!(
    ParametrizedOp<T>,
    values: PtrAndStrideWrappingMatrix<T>,
    param: u32,
    result: MutPtrAndStrideWrappingMatrix<T>,
);

macro_rules! parametrized_op_kernel {
    ($op:ty, $type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_ $op:lower _ $type:lower _kernel>](
                    values: PtrAndStrideWrappingMatrix<$type>,
                    param: u32,
                    result: MutPtrAndStrideWrappingMatrix<$type>,
                )
            );
        }
    };
}

pub trait ParametrizedOp<T> {
    const KERNEL_FUNCTION: ParametrizedOpSignature<T>;

    fn launch_op(
        values: PtrAndStrideWrappingMatrix<T>,
        param: u32,
        result: MutPtrAndStrideWrappingMatrix<T>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let (grid_dim, block_dim) = get_launch_dims(result.rows, result.cols);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = ParametrizedOpArguments::<T>::new(values, param, result);
        ParametrizedOpFunction::<T>(Self::KERNEL_FUNCTION).launch(&config, &args)
    }

    fn launch(
        values: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
        param: u32,
        result: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
        stream: &CudaStream,
    ) -> CudaResult<()> {
        assert_eq!(result.rows() % values.rows(), 0);
        assert_eq!(result.cols() % values.cols(), 0);
        Self::launch_op(
            PtrAndStrideWrappingMatrix::new(values),
            param,
            MutPtrAndStrideWrappingMatrix::new(result),
            stream,
        )
    }
}

macro_rules! parametrized_op_def {
    ($op:ty) => {
        paste! {
            pub struct $op;
            #[allow(dead_code)]
            pub fn [<$op:lower>]<T>(
                values: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
                param: u32,
                result: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()>  where $op: ParametrizedOp<T> {
                $op::launch(values, param, result, stream)
            }
        }
    };
}

parametrized_op_def!(Pow);

macro_rules! parametrized_op_impl {
    ($op:ty, $type:ty) => {
        paste! {
            parametrized_op_kernel!($op, $type);
            impl ParametrizedOp<$type> for $op {
                const KERNEL_FUNCTION: ParametrizedOpSignature<$type> = [<ab_ $op:lower _ $type:lower _kernel>];
            }
        }
    };
}

macro_rules! parametrized_ops_impl {
    ($type:ty) => {
        parametrized_op_impl!(Pow, $type);
    };
}

parametrized_ops_impl!(BF);
parametrized_ops_impl!(E2);
parametrized_ops_impl!(E4);
parametrized_ops_impl!(E6);

// BINARY_KERNEL
cuda_kernel_signature_arguments_and_function!(
    BinaryOp<T0, T1, TR>,
    x: PtrAndStrideWrappingMatrix<T0>,
    y: PtrAndStrideWrappingMatrix<T1>,
    result: MutPtrAndStrideWrappingMatrix<TR>,
);

macro_rules! binary_op_kernel {
    ($op:ty, $t0:ty, $t1:ty, $tr:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_ $op:lower _ $t0:lower _ $t1:lower _kernel>](
                    x: PtrAndStrideWrappingMatrix<$t0>,
                    y: PtrAndStrideWrappingMatrix<$t1>,
                    result: MutPtrAndStrideWrappingMatrix<$tr>,
                )
            );
        }
    };
}

pub trait BinaryOp<T0, T1, TR> {
    const KERNEL_FUNCTION: BinaryOpSignature<T0, T1, TR>;

    fn launch_op(
        x: PtrAndStrideWrappingMatrix<T0>,
        y: PtrAndStrideWrappingMatrix<T1>,
        result: MutPtrAndStrideWrappingMatrix<TR>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let (grid_dim, block_dim) = get_launch_dims(result.rows, result.cols);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = BinaryOpArguments::<T0, T1, TR>::new(x, y, result);
        BinaryOpFunction::<T0, T1, TR>(Self::KERNEL_FUNCTION).launch(&config, &args)
    }

    fn launch(
        x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
        y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
        result: &mut (impl DeviceMatrixChunkMutImpl<TR> + ?Sized),
        stream: &CudaStream,
    ) -> CudaResult<()> {
        assert_eq!(result.rows() % x.rows(), 0);
        assert_eq!(result.cols() % x.cols(), 0);
        assert_eq!(result.rows() % y.rows(), 0);
        assert_eq!(result.cols() % y.cols(), 0);
        Self::launch_op(
            PtrAndStrideWrappingMatrix::new(x),
            PtrAndStrideWrappingMatrix::new(y),
            MutPtrAndStrideWrappingMatrix::new(result),
            stream,
        )
    }

    fn launch_into_x(
        x: &mut (impl DeviceMatrixChunkMutImpl<T0> + ?Sized),
        y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
        stream: &CudaStream,
    ) -> CudaResult<()>
    where
        Self: BinaryOp<T0, T1, T0>,
    {
        <Self as BinaryOp<T0, T1, T0>>::launch_op(
            PtrAndStrideWrappingMatrix::new(x),
            PtrAndStrideWrappingMatrix::new(y),
            MutPtrAndStrideWrappingMatrix::new(x),
            stream,
        )
    }

    fn launch_into_y(
        x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
        y: &mut (impl DeviceMatrixChunkMutImpl<T1> + ?Sized),
        stream: &CudaStream,
    ) -> CudaResult<()>
    where
        Self: BinaryOp<T0, T1, T1>,
    {
        <Self as BinaryOp<T0, T1, T1>>::launch_op(
            PtrAndStrideWrappingMatrix::new(x),
            PtrAndStrideWrappingMatrix::new(y),
            MutPtrAndStrideWrappingMatrix::new(y),
            stream,
        )
    }
}

macro_rules! binary_op_def {
    ($op:ty) => {
        paste! {
            pub struct $op;
            #[allow(dead_code)]
            pub fn [<$op:lower>]<T0, T1, TR>(
                x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
                y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
                result: &mut (impl DeviceMatrixChunkMutImpl<TR> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()> where $op: BinaryOp<T0, T1, TR> {
                $op::launch(x, y, result, stream)
            }
            #[allow(dead_code)]
            pub fn [<$op:lower _into_x>]<T0, T1>(
                x: &mut (impl DeviceMatrixChunkMutImpl<T0> + ?Sized),
                y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()>  where $op: BinaryOp<T0, T1, T0> {
                $op::launch_into_x(x, y, stream)
            }
            #[allow(dead_code)]
            pub fn [<$op:lower _into_y>]<T0, T1>(
                x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
                y: &mut (impl DeviceMatrixChunkMutImpl<T1> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()>  where $op: BinaryOp<T0, T1, T1> {
                $op::launch_into_y(x, y, stream)
            }
        }
    };
}

binary_op_def!(Add);
binary_op_def!(Mul);
binary_op_def!(Sub);

macro_rules! binary_op_impl {
    ($op:ty, $t0:ty, $t1:ty, $tr:ty) => {
        paste! {
            binary_op_kernel!($op, $t0, $t1, $tr);
            impl BinaryOp<$t0, $t1, $tr> for $op {
                const KERNEL_FUNCTION: BinaryOpSignature<$t0, $t1, $tr> = [<ab_ $op:lower _ $t0:lower _ $t1:lower _kernel>];
            }
        }
    };
}

macro_rules! binary_ops_impl {
    ($t0:ty, $t1:ty, $tr:ty) => {
        binary_op_impl!(Add, $t0, $t1, $tr);
        binary_op_impl!(Mul, $t0, $t1, $tr);
        binary_op_impl!(Sub, $t0, $t1, $tr);
    };
}

binary_ops_impl!(BF, BF, BF);
binary_ops_impl!(BF, E4, E4);
binary_ops_impl!(E2, E2, E2);
binary_ops_impl!(E4, BF, E4);
binary_ops_impl!(E4, E4, E4);
binary_ops_impl!(E6, E6, E6);

#[cfg(test)]
mod tests;
