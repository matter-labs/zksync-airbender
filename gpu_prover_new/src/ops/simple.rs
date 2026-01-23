use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::memory::memory_set_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStrideWrappingMatrix,
    PtrAndStrideWrappingMatrix,
};
use crate::field::{BF, E2, E4, E6};
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

pub fn set_to_zero<T>(result: &mut DeviceSlice<T>, stream: &CudaStream) -> CudaResult<()> {
    memory_set_async(unsafe { result.transmute_mut() }, 0, stream)
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

// UNARY_KERNEL
cuda_kernel_signature_arguments_and_function!(
    UnaryOp<T>,
    values: PtrAndStrideWrappingMatrix<T>,
    result: MutPtrAndStrideWrappingMatrix<T>,
);

macro_rules! unary_op_kernel {
    ($op:ty, $type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_ $op:lower _ $type:lower _kernel>](
                    values: PtrAndStrideWrappingMatrix<$type>,
                    result: MutPtrAndStrideWrappingMatrix<$type>,
                )
            );
        }
    };
}

pub trait UnaryOp<T> {
    const KERNEL_FUNCTION: UnaryOpSignature<T>;

    fn launch_op(
        values: PtrAndStrideWrappingMatrix<T>,
        result: MutPtrAndStrideWrappingMatrix<T>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let (grid_dim, block_dim) = get_launch_dims(result.rows, result.cols);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = UnaryOpArguments::<T>::new(values, result);
        UnaryOpFunction::<T>(Self::KERNEL_FUNCTION).launch(&config, &args)
    }

    fn launch(
        values: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
        result: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
        stream: &CudaStream,
    ) -> CudaResult<()> {
        assert_eq!(result.rows() % values.rows(), 0);
        assert_eq!(result.cols() % values.cols(), 0);
        Self::launch_op(
            PtrAndStrideWrappingMatrix::new(values),
            MutPtrAndStrideWrappingMatrix::new(result),
            stream,
        )
    }

    fn launch_in_place(
        values: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
        stream: &CudaStream,
    ) -> CudaResult<()> {
        Self::launch_op(
            PtrAndStrideWrappingMatrix::new(values),
            MutPtrAndStrideWrappingMatrix::new(values),
            stream,
        )
    }
}

macro_rules! unary_op_def {
    ($op:ty) => {
        paste! {
            pub struct $op;
            pub fn [<$op:lower>]<T>(
                values: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
                result: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()> where $op: UnaryOp<T> {
                $op::launch(values, result, stream)
            }
            pub fn [<$op:lower _in_place>]<T>(
                values: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()>  where $op: UnaryOp<T> {
                $op::launch_in_place(values, stream)
            }
        }
    };
}

unary_op_def!(Dbl);
unary_op_def!(Inv);
unary_op_def!(Neg);
unary_op_def!(Sqr);

macro_rules! unary_op_impl {
    ($op:ty, $type:ty) => {
        paste! {
            unary_op_kernel!($op, $type);
            impl UnaryOp<$type> for $op {
                const KERNEL_FUNCTION: UnaryOpSignature<$type> = [<ab_ $op:lower _ $type:lower _kernel>];
            }
        }
    };
}

macro_rules! unary_ops_impl {
    ($type:ty) => {
        unary_op_impl!(Dbl, $type);
        unary_op_impl!(Inv, $type);
        unary_op_impl!(Neg, $type);
        unary_op_impl!(Sqr, $type);
    };
}

unary_ops_impl!(BF);
unary_ops_impl!(E2);
unary_ops_impl!(E4);
unary_ops_impl!(E6);

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

    fn launch_in_place(
        values: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
        param: u32,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        Self::launch_op(
            PtrAndStrideWrappingMatrix::new(values),
            param,
            MutPtrAndStrideWrappingMatrix::new(values),
            stream,
        )
    }
}

macro_rules! parametrized_op_def {
    ($op:ty) => {
        paste! {
            pub struct $op;
            pub fn [<$op:lower>]<T>(
                values: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
                param: u32,
                result: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()>  where $op: ParametrizedOp<T> {
                $op::launch(values, param, result, stream)
            }
            pub fn [<$op:lower _in_place>]<T>(
                values: &mut (impl DeviceMatrixChunkMutImpl<T> + ?Sized),
                param: u32,
                stream: &CudaStream,
            ) -> CudaResult<()>  where $op: ParametrizedOp<T> {
                $op::launch_in_place(values, param, stream)
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
            pub fn [<$op:lower>]<T0, T1, TR>(
                x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
                y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
                result: &mut (impl DeviceMatrixChunkMutImpl<TR> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()> where $op: BinaryOp<T0, T1, TR> {
                $op::launch(x, y, result, stream)
            }
            pub fn [<$op:lower _into_x>]<T0, T1>(
                x: &mut (impl DeviceMatrixChunkMutImpl<T0> + ?Sized),
                y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
                stream: &CudaStream,
            ) -> CudaResult<()>  where $op: BinaryOp<T0, T1, T0> {
                $op::launch_into_x(x, y, stream)
            }
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
binary_ops_impl!(BF, E2, E2);
binary_ops_impl!(BF, E4, E4);
binary_ops_impl!(BF, E6, E6);
binary_ops_impl!(E2, BF, E2);
binary_ops_impl!(E2, E2, E2);
binary_ops_impl!(E2, E4, E4);
binary_ops_impl!(E2, E6, E6);
binary_ops_impl!(E4, BF, E4);
binary_ops_impl!(E4, E2, E4);
binary_ops_impl!(E4, E4, E4);
binary_ops_impl!(E4, E6, E6);
binary_ops_impl!(E6, BF, E6);
binary_ops_impl!(E6, E2, E6);
binary_ops_impl!(E6, E4, E6);
binary_ops_impl!(E6, E6, E6);

// // TERNARY_KERNEL
// cuda_kernel_signature_arguments_and_function!(
//     TernaryOp<T0, T1, T2, TR>,
//     x: PtrAndStrideWrappingMatrix<T0>,
//     y: PtrAndStrideWrappingMatrix<T1>,
//     z: PtrAndStrideWrappingMatrix<T2>,
//     result: MutPtrAndStrideWrappingMatrix<TR>,
// );
//
// macro_rules! ternary_op_kernel {
//     ($fn_name:ident, $t0:ty, $t1:ty, $t2:ty, $tr:ty) => {
//         paste! {
//             cuda_kernel_declaration!(
//                 [<ab_ $fn_name _ $t0:lower _ $t1:lower _ $t2:lower _kernel>](
//                     x: PtrAndStrideWrappingMatrix<$t0>,
//                     y: PtrAndStrideWrappingMatrix<$t1>,
//                     z: PtrAndStrideWrappingMatrix<$t2>,
//                     result: MutPtrAndStrideWrappingMatrix<$tr>,
//                 )
//             );
//         }
//     };
// }
//
// pub trait TernaryOp<T0, T1, T2, TR> {
//     fn get_kernel_function() -> TernaryOpSignature<T0, T1, T2, TR>;
//
//     fn launch_op(
//         x: PtrAndStrideWrappingMatrix<T0>,
//         y: PtrAndStrideWrappingMatrix<T1>,
//         z: PtrAndStrideWrappingMatrix<T2>,
//         result: MutPtrAndStrideWrappingMatrix<TR>,
//         stream: &CudaStream,
//     ) -> CudaResult<()> {
//         let kernel_function = Self::get_kernel_function();
//         let (grid_dim, block_dim) = get_launch_dims(result.rows, result.cols);
//         let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
//         let args = TernaryOpArguments::<T0, T1, T2, TR>::new(x, y, z, result);
//         TernaryOpFunction::<T0, T1, T2, TR>(kernel_function).launch(&config, &args)
//     }
//
//     fn launch(
//         x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
//         y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
//         z: &(impl DeviceMatrixChunkImpl<T2> + ?Sized),
//         result: &mut (impl DeviceMatrixChunkMutImpl<TR> + ?Sized),
//         stream: &CudaStream,
//     ) -> CudaResult<()> {
//         assert_eq!(result.rows() % x.rows(), 0);
//         assert_eq!(result.cols() % x.cols(), 0);
//         assert_eq!(result.rows() % y.rows(), 0);
//         assert_eq!(result.cols() % y.cols(), 0);
//         assert_eq!(result.rows() % z.rows(), 0);
//         assert_eq!(result.cols() % z.cols(), 0);
//         Self::launch_op(
//             PtrAndStrideWrappingMatrix::new(x),
//             PtrAndStrideWrappingMatrix::new(y),
//             PtrAndStrideWrappingMatrix::new(z),
//             MutPtrAndStrideWrappingMatrix::new(result),
//             stream,
//         )
//     }
//
//     fn launch_into_x(
//         x: &mut (impl DeviceMatrixChunkMutImpl<T0> + ?Sized),
//         y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
//         z: &(impl DeviceMatrixChunkImpl<T2> + ?Sized),
//         stream: &CudaStream,
//     ) -> CudaResult<()>
//     where
//         Self: TernaryOp<T0, T1, T2, T0>,
//     {
//         <Self as TernaryOp<T0, T1, T2, T0>>::launch_op(
//             PtrAndStrideWrappingMatrix::new(x),
//             PtrAndStrideWrappingMatrix::new(y),
//             PtrAndStrideWrappingMatrix::new(z),
//             MutPtrAndStrideWrappingMatrix::new(x),
//             stream,
//         )
//     }
//
//     fn launch_into_y(
//         x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
//         y: &mut (impl DeviceMatrixChunkMutImpl<T1> + ?Sized),
//         z: &(impl DeviceMatrixChunkImpl<T2> + ?Sized),
//         stream: &CudaStream,
//     ) -> CudaResult<()>
//     where
//         Self: TernaryOp<T0, T1, T2, T1>,
//     {
//         <Self as TernaryOp<T0, T1, T2, T1>>::launch_op(
//             PtrAndStrideWrappingMatrix::new(x),
//             PtrAndStrideWrappingMatrix::new(y),
//             PtrAndStrideWrappingMatrix::new(z),
//             MutPtrAndStrideWrappingMatrix::new(y),
//             stream,
//         )
//     }
//
//     fn launch_into_z(
//         x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
//         y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
//         z: &mut (impl DeviceMatrixChunkMutImpl<T2> + ?Sized),
//         stream: &CudaStream,
//     ) -> CudaResult<()>
//     where
//         Self: TernaryOp<T0, T1, T2, T2>,
//     {
//         <Self as TernaryOp<T0, T1, T2, T2>>::launch_op(
//             PtrAndStrideWrappingMatrix::new(x),
//             PtrAndStrideWrappingMatrix::new(y),
//             PtrAndStrideWrappingMatrix::new(z),
//             MutPtrAndStrideWrappingMatrix::new(z),
//             stream,
//         )
//     }
// }
//
// macro_rules! ternary_op_def {
//     ($op:ty, $fn_name:ident) => {
//         paste! {
//             pub struct $op;
//             pub fn $fn_name<T0, T1, T2, TR>(
//                 x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
//                 y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
//                 z: &(impl DeviceMatrixChunkImpl<T2> + ?Sized),
//                 result: &mut (impl DeviceMatrixChunkMutImpl<TR> + ?Sized),
//                 stream: &CudaStream,
//             ) -> CudaResult<()> where $op: TernaryOp<T0, T1, T2, TR> {
//                 $op::launch(x, y, z, result, stream)
//             }
//             pub fn [<$fn_name _into_x>]<T0, T1, T2>(
//                 x: &mut (impl DeviceMatrixChunkMutImpl<T0> + ?Sized),
//                 y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
//                 z: &(impl DeviceMatrixChunkImpl<T2> + ?Sized),
//                 stream: &CudaStream,
//             ) -> CudaResult<()>  where $op: TernaryOp<T0, T1, T2, T0> {
//                 $op::launch_into_x(x, y, z, stream)
//             }
//             pub fn [<$fn_name _into_y>]<T0, T1, T2>(
//                 x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
//                 y: &mut (impl DeviceMatrixChunkMutImpl<T1> + ?Sized),
//                 z: &(impl DeviceMatrixChunkImpl<T2> + ?Sized),
//                 stream: &CudaStream,
//             ) -> CudaResult<()>  where $op: TernaryOp<T0, T1, T2, T1> {
//                 $op::launch_into_y(x, y, z, stream)
//             }
//             pub fn [<$fn_name _into_z>]<T0, T1, T2>(
//                 x: &(impl DeviceMatrixChunkImpl<T0> + ?Sized),
//                 y: &(impl DeviceMatrixChunkImpl<T1> + ?Sized),
//                 z: &mut (impl DeviceMatrixChunkMutImpl<T2> + ?Sized),
//                 stream: &CudaStream,
//             ) -> CudaResult<()>  where $op: TernaryOp<T0, T1, T2, T2> {
//                 $op::launch_into_z(x, y, z, stream)
//             }
//         }
//     };
// }
//
// ternary_op_def!(MulAdd, mul_add);
// ternary_op_def!(MulSub, mul_sub);
//
// macro_rules! ternary_op_impl {
//     ($op:ty, $fn_name:ident, $t0:ty, $t1:ty, $t2:ty, $tr:ty) => {
//         paste! {
//             ternary_op_kernel!($fn_name, $t0, $t1, $t2, $tr);
//             impl TernaryOp<$t0, $t1, $t2, $tr> for $op {
//                 fn get_kernel_function() -> TernaryOpSignature<$t0, $t1, $t2, $tr> {
//                     [<ab_ $fn_name _ $t0:lower _ $t1:lower _ $t2:lower _kernel>]
//                 }
//             }
//         }
//     };
// }
//
// macro_rules! ternary_ops_impl {
//     ($t0:ty, $t1:ty, $t2:ty, $tr:ty) => {
//         ternary_op_impl!(MulAdd, mul_add, $t0, $t1, $t2, $tr);
//         ternary_op_impl!(MulSub, mul_sub, $t0, $t1, $t2, $tr);
//     };
// }
//
// ternary_ops_impl!(BF, BF, BF, BF);
// ternary_ops_impl!(BF, BF, E2, E2);
// ternary_ops_impl!(BF, BF, E4, E4);
// ternary_ops_impl!(BF, E2, BF, E2);
// ternary_ops_impl!(BF, E2, E2, E2);
// ternary_ops_impl!(BF, E2, E4, E4);
// ternary_ops_impl!(BF, E4, BF, E4);
// ternary_ops_impl!(BF, E4, E2, E4);
// ternary_ops_impl!(BF, E4, E4, E4);
// ternary_ops_impl!(E2, BF, BF, E2);
// ternary_ops_impl!(E2, BF, E2, E2);
// ternary_ops_impl!(E2, BF, E4, E4);
// ternary_ops_impl!(E2, E2, BF, E2);
// ternary_ops_impl!(E2, E2, E2, E2);
// ternary_ops_impl!(E2, E2, E4, E4);
// ternary_ops_impl!(E2, E4, BF, E4);
// ternary_ops_impl!(E2, E4, E2, E4);
// ternary_ops_impl!(E2, E4, E4, E4);
// ternary_ops_impl!(E4, BF, BF, E4);
// ternary_ops_impl!(E4, BF, E2, E4);
// ternary_ops_impl!(E4, BF, E4, E4);
// ternary_ops_impl!(E4, E2, BF, E4);
// ternary_ops_impl!(E4, E2, E2, E4);
// ternary_ops_impl!(E4, E2, E4, E4);
// ternary_ops_impl!(E4, E4, BF, E4);
// ternary_ops_impl!(E4, E4, E2, E4);
// ternary_ops_impl!(E4, E4, E4, E4);

#[cfg(test)]
mod tests {
    use crate::field::{BF, E2, E4, E6};
    use crate::ops::simple::{
        Add, BinaryOp, Dbl, Inv, Mul, Neg, SetByRef, SetByVal, Sqr, Sub, UnaryOp,
    };
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use era_cudart::result::CudaResult;
    use era_cudart::slice::DeviceSlice;
    use era_cudart::stream::CudaStream;
    use field::{Field, Rand};
    use itertools::Itertools;

    fn set_by_val<T: Field + SetByVal, const LOG_N: u32>() {
        let n = 1 << LOG_N;
        let value = T::ONE;
        let stream = CudaStream::default();
        let mut dst_host = vec![T::ZERO; n];
        let mut dst_device = DeviceAllocation::alloc(n).unwrap();
        memory_copy_async(&mut dst_device, &dst_host, &stream).unwrap();
        super::set_by_val(value, &mut dst_device, &stream).unwrap();
        memory_copy_async(&mut dst_host, &dst_device, &stream).unwrap();
        stream.synchronize().unwrap();
        assert!(dst_host.iter().all(|x| { x.eq(&value) }));
    }

    #[test]
    fn set_by_val_bf() {
        set_by_val::<BF, 20>();
    }

    #[test]
    fn set_by_val_e2() {
        set_by_val::<E2, 19>();
    }

    #[test]
    fn set_by_val_e4() {
        set_by_val::<E4, 18>();
    }

    #[test]
    fn set_by_val_e6() {
        set_by_val::<E6, 18>();
    }

    fn set_by_ref<T: Field + SetByVal + SetByRef, const LOG_N: u32>() {
        let n = 1 << LOG_N;
        let value = T::ONE;
        let stream = CudaStream::default();
        let mut value_device = DeviceAllocation::alloc(1).unwrap();
        super::set_by_val(value, &mut value_device, &stream).unwrap();
        let mut dst_host = vec![T::ZERO; n];
        let mut dst_device = DeviceAllocation::alloc(n).unwrap();
        memory_copy_async(&mut dst_device, &dst_host, &stream).unwrap();
        super::set_by_ref(&value_device, &mut dst_device, &stream).unwrap();
        memory_copy_async(&mut dst_host, &dst_device, &stream).unwrap();
        stream.synchronize().unwrap();
        assert!(dst_host.iter().all(|x| { x.eq(&value) }));
    }

    #[test]
    fn set_by_ref_bf() {
        set_by_ref::<BF, 20>();
    }

    #[test]
    fn set_by_ref_e2() {
        set_by_ref::<E2, 19>();
    }

    #[test]
    fn set_by_ref_e4() {
        set_by_ref::<E4, 18>();
    }

    #[test]
    fn set_by_ref_e6() {
        set_by_ref::<E6, 18>();
    }

    fn set_to_zero<T: Field, const LOG_N: u32>() {
        let n = 1 << 18;
        let stream = CudaStream::default();
        let mut dst_host = vec![T::ONE; n];
        let mut dst_device = DeviceAllocation::alloc(n).unwrap();
        memory_copy_async(&mut dst_device, &dst_host, &stream).unwrap();
        super::set_to_zero(&mut dst_device, &stream).unwrap();
        memory_copy_async(&mut dst_host, &dst_device, &stream).unwrap();
        stream.synchronize().unwrap();
        assert!(dst_host.iter().all(|x| { x.eq(&T::ZERO) }));
    }

    #[test]
    fn set_to_zero_bf() {
        set_to_zero::<BF, 20>();
    }

    #[test]
    fn set_to_zero_e2() {
        set_to_zero::<E2, 19>();
    }

    #[test]
    fn set_to_zero_e4() {
        set_to_zero::<E4, 18>();
    }

    fn set_to_zero_e6() {
        set_to_zero::<E6, 18>();
    }

    type UnaryDeviceFn<T> = fn(&DeviceSlice<T>, &mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

    type UnaryDeviceInPlaceFn<T> = fn(&mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

    type UnaryHostFn<T> = fn(&T) -> T;

    type ParametrizedUnaryDeviceFn<T> =
        fn(&DeviceSlice<T>, u32, &mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

    type ParametrizedUnaryDeviceInPlaceFn<T> =
        fn(&mut DeviceSlice<T>, u32, &CudaStream) -> CudaResult<()>;

    type ParametrizedUnaryHostFn<T> = fn(&T, u32) -> T;

    type BinaryDeviceFn<T> =
        fn(&DeviceSlice<T>, &DeviceSlice<T>, &mut DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

    type BinaryDeviceInPlaceFn<T> =
        fn(&mut DeviceSlice<T>, &DeviceSlice<T>, &CudaStream) -> CudaResult<()>;

    type BinaryHostFn<T> = fn(&T, &T) -> T;

    // type TernaryDeviceFn = fn(
    //     &DeviceSlice<BF>,
    //     &DeviceSlice<BF>,
    //     &DeviceSlice<BF>,
    //     &mut DeviceSlice<BF>,
    //     &CudaStream,
    // ) -> CudaResult<()>;
    //
    // type TernaryDeviceInPlaceFn =
    //     fn(&mut DeviceSlice<BF>, &DeviceSlice<BF>, &DeviceSlice<BF>, &CudaStream) -> CudaResult<()>;
    //
    // type TernaryHostFn = fn(&BF, &BF, &BF) -> BF;

    fn unary_op_test<T: Field, const LOG_N: u32>(
        device_fn: UnaryDeviceFn<T>,
        host_fn: UnaryHostFn<T>,
        additional_values: &[T],
    ) {
        let n = 1 << LOG_N;
        let x_host = get_values(n, additional_values);
        let stream = CudaStream::default();
        let mut result_host = vec![T::ZERO; n];
        let mut x_device = DeviceAllocation::alloc(n).unwrap();
        let mut result_device = DeviceAllocation::alloc(n).unwrap();
        memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
        device_fn(&x_device, &mut result_device, &stream).unwrap();
        memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for i in 0..n {
            let left = host_fn(&x_host[i]);
            let right = result_host[i];
            assert_eq!(left, right, "i = {}", i);
        }
    }

    fn unary_op_in_place_test<T: Field, const LOG_N: u32>(
        device_fn: UnaryDeviceInPlaceFn<T>,
        host_fn: UnaryHostFn<T>,
        additional_values: &[T],
    ) {
        let n = 1 << LOG_N;
        let x_host = get_values(n, additional_values);
        let stream = CudaStream::default();
        let mut result_host = vec![T::ZERO; n];
        let mut x_device = DeviceAllocation::alloc(n).unwrap();
        memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
        device_fn(&mut x_device, &stream).unwrap();
        memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for i in 0..n {
            let left = host_fn(&x_host[i]);
            let right = result_host[i];
            assert_eq!(left, right, "i = {}", i);
        }
    }

    fn parametrized_unary_op_test<T: Field, const LOG_N: u32>(
        parameter: u32,
        device_fn: ParametrizedUnaryDeviceFn<T>,
        host_fn: ParametrizedUnaryHostFn<T>,
        additional_values: &[T],
    ) {
        let n = 1 << LOG_N;
        let x_host = get_values(n, additional_values);
        let stream = CudaStream::default();
        let mut result_host = vec![T::ZERO; n];
        let mut x_device = DeviceAllocation::alloc(n).unwrap();
        let mut result_device = DeviceAllocation::alloc(n).unwrap();
        memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
        device_fn(&x_device, parameter, &mut result_device, &stream).unwrap();
        memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for i in 0..n {
            let left = host_fn(&x_host[i], parameter);
            let right = result_host[i];
            assert_eq!(left, right, "i = {}", i);
        }
    }

    fn parametrized_unary_op_in_place_test<T: Field, const LOG_N: u32>(
        parameter: u32,
        device_fn: ParametrizedUnaryDeviceInPlaceFn<T>,
        host_fn: ParametrizedUnaryHostFn<T>,
        additional_values: &[T],
    ) {
        let n = 1 << LOG_N;
        let x_host = get_values(n, additional_values);
        let stream = CudaStream::default();
        let mut result_host = vec![T::ZERO; n];
        let mut x_device = DeviceAllocation::alloc(n).unwrap();
        memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
        device_fn(&mut x_device, parameter, &stream).unwrap();
        memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for i in 0..n {
            let left = host_fn(&x_host[i], parameter);
            let right = result_host[i];
            assert_eq!(left, right, "i = {}", i);
        }
    }

    fn binary_op_test<T: Field, const LOG_N: u32>(
        device_fn: BinaryDeviceFn<T>,
        host_fn: BinaryHostFn<T>,
        additional_values: &[T],
    ) {
        let n = 1 << LOG_N;
        let values = get_values(n, additional_values);
        let mut x_host = Vec::new();
        let mut y_host = Vec::new();
        values
            .iter()
            .cartesian_product(values.iter())
            .for_each(|(&x, &y)| {
                x_host.push(x);
                y_host.push(y);
            });
        let stream = CudaStream::default();
        let length = x_host.len();
        let mut result_host = vec![T::ZERO; length];
        let mut x_device = DeviceAllocation::alloc(length).unwrap();
        let mut y_device = DeviceAllocation::alloc(length).unwrap();
        let mut result_device = DeviceAllocation::alloc(length).unwrap();
        memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
        memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
        device_fn(&x_device, &y_device, &mut result_device, &stream).unwrap();
        memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for i in 0..length {
            let left = host_fn(&x_host[i], &y_host[i]);
            let right = result_host[i];
            assert_eq!(left, right, "i = {}", i);
        }
    }

    fn binary_op_in_place_test<T: Field, const LOG_N: u32>(
        device_fn: BinaryDeviceInPlaceFn<T>,
        host_fn: BinaryHostFn<T>,
        additional_values: &[T],
    ) {
        let n = 1 << LOG_N;
        let values = get_values(n, additional_values);
        let mut x_host = Vec::new();
        let mut y_host = Vec::new();
        values
            .iter()
            .cartesian_product(values.iter())
            .for_each(|(&x, &y)| {
                x_host.push(x);
                y_host.push(y);
            });
        let stream = CudaStream::default();
        let length = x_host.len();
        let mut result_host = vec![T::ZERO; length];
        let mut x_device = DeviceAllocation::alloc(length).unwrap();
        let mut y_device = DeviceAllocation::alloc(length).unwrap();
        memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
        memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
        device_fn(&mut x_device, &y_device, &stream).unwrap();
        memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
        stream.synchronize().unwrap();
        for i in 0..length {
            let left = host_fn(&x_host[i], &y_host[i]);
            let right = result_host[i];
            assert_eq!(left, right, "i = {}", i);
        }
    }

    // fn ternary_op_test(device_fn: TernaryDeviceFn, host_fn: TernaryHostFn) {
    //     const VALUES_COUNT: usize = 1 << 6;
    //     let values = get_values(VALUES_COUNT);
    //     let mut x_host = vec![];
    //     let mut y_host = vec![];
    //     let mut z_host = vec![];
    //     values
    //         .iter()
    //         .cartesian_product(values.iter())
    //         .cartesian_product(values.iter())
    //         .for_each(|((&x, &y), &z)| {
    //             x_host.push(x);
    //             y_host.push(y);
    //             z_host.push(z);
    //         });
    //     let stream = CudaStream::default();
    //     let length = x_host.len();
    //     let mut result_host = vec![BF::ZERO; length];
    //     let mut x_device = DeviceAllocation::alloc(length).unwrap();
    //     let mut y_device = DeviceAllocation::alloc(length).unwrap();
    //     let mut z_device = DeviceAllocation::alloc(length).unwrap();
    //     let mut result_device = DeviceAllocation::alloc(length).unwrap();
    //     memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    //     memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
    //     memory_copy_async(&mut z_device, &z_host, &stream).unwrap();
    //     device_fn(&x_device, &y_device, &z_device, &mut result_device, &stream).unwrap();
    //     memory_copy_async(&mut result_host, &result_device, &stream).unwrap();
    //     stream.synchronize().unwrap();
    //     for i in 0..length {
    //         let left = host_fn(&x_host[i], &y_host[i], &z_host[i]);
    //         let right = result_host[i];
    //         assert_eq!(left, right, "i = {}", i);
    //     }
    // }
    //
    // fn ternary_op_in_place_test(device_fn: TernaryDeviceInPlaceFn, host_fn: TernaryHostFn) {
    //     const VALUES_COUNT: usize = 1 << 6;
    //     let values = get_values(VALUES_COUNT);
    //     let mut x_host = vec![];
    //     let mut y_host = vec![];
    //     let mut z_host = vec![];
    //     values
    //         .iter()
    //         .cartesian_product(values.iter())
    //         .cartesian_product(values.iter())
    //         .for_each(|((&x, &y), &z)| {
    //             x_host.push(x);
    //             y_host.push(y);
    //             z_host.push(z);
    //         });
    //     let stream = CudaStream::default();
    //     let length = x_host.len();
    //     let mut result_host = vec![BF::ZERO; length];
    //     let mut x_device = DeviceAllocation::alloc(length).unwrap();
    //     let mut y_device = DeviceAllocation::alloc(length).unwrap();
    //     let mut z_device = DeviceAllocation::alloc(length).unwrap();
    //     memory_copy_async(&mut x_device, &x_host, &stream).unwrap();
    //     memory_copy_async(&mut y_device, &y_host, &stream).unwrap();
    //     memory_copy_async(&mut z_device, &z_host, &stream).unwrap();
    //     device_fn(&mut x_device, &y_device, &z_device, &stream).unwrap();
    //     memory_copy_async(&mut result_host, &x_device, &stream).unwrap();
    //     stream.synchronize().unwrap();
    //     for i in 0..length {
    //         let left = host_fn(&x_host[i], &y_host[i], &z_host[i]);
    //         let right = result_host[i];
    //         assert_eq!(left, right, "i = {}", i);
    //     }
    // }

    const BF_VALUES: [BF; 6] = [
        BF::new(0),
        BF::new(1),
        BF::new(2),
        BF::new(BF::ORDER - 3),
        BF::new(BF::ORDER - 2),
        BF::new(BF::ORDER - 1),
    ];

    const E2_VALUES: [E2; 6] = [
        E2::new(BF_VALUES[0], BF_VALUES[0]),
        E2::new(BF_VALUES[1], BF_VALUES[1]),
        E2::new(BF_VALUES[2], BF_VALUES[2]),
        E2::new(BF_VALUES[3], BF_VALUES[3]),
        E2::new(BF_VALUES[4], BF_VALUES[4]),
        E2::new(BF_VALUES[5], BF_VALUES[5]),
    ];

    const E4_VALUES: [E4; 6] = [
        E4::new(E2_VALUES[0], E2_VALUES[0]),
        E4::new(E2_VALUES[1], E2_VALUES[1]),
        E4::new(E2_VALUES[2], E2_VALUES[2]),
        E4::new(E2_VALUES[3], E2_VALUES[3]),
        E4::new(E2_VALUES[4], E2_VALUES[4]),
        E4::new(E2_VALUES[5], E2_VALUES[5]),
    ];

    const E6_VALUES: [E6; 6] = [
        E6::new(E2_VALUES[0], E2_VALUES[0], E2_VALUES[0]),
        E6::new(E2_VALUES[1], E2_VALUES[1], E2_VALUES[1]),
        E6::new(E2_VALUES[2], E2_VALUES[2], E2_VALUES[2]),
        E6::new(E2_VALUES[3], E2_VALUES[3], E2_VALUES[3]),
        E6::new(E2_VALUES[4], E2_VALUES[4], E2_VALUES[4]),
        E6::new(E2_VALUES[5], E2_VALUES[5], E2_VALUES[5]),
    ];

    fn get_values<T: Field>(count: usize, additional_values: &[T]) -> Vec<T> {
        assert!(count >= additional_values.len());
        let mut rng = rand::rng();
        let mut values: Vec<T> = (0..count - additional_values.len())
            .map(|_| T::random_element(&mut rng))
            .collect();
        values.extend_from_slice(additional_values);
        values
    }

    fn dbl<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Dbl: UnaryOp<T>,
    {
        let device_fn = super::dbl;
        let host_fn = |x: &T| *x.clone().double();
        unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn dbl_bf() {
        dbl::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn dbl_e2() {
        dbl::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn dbl_e4() {
        dbl::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn dbl_e6() {
        dbl::<E6, 18>(&E6_VALUES);
    }

    fn dbl_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Dbl: UnaryOp<T>,
    {
        let device_fn = super::dbl_in_place;
        let host_fn = |x: &T| *x.clone().double();
        unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn dbl_in_place_bf() {
        dbl_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn dbl_in_place_e2() {
        dbl_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn dbl_in_place_e4() {
        dbl_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn dbl_in_place_e6() {
        dbl_in_place::<E6, 18>(&E6_VALUES);
    }

    fn inv<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Inv: UnaryOp<T>,
    {
        let device_fn = super::inv;
        let host_fn = |x: &T| x.inverse().unwrap_or(T::ZERO);
        unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn inv_bf() {
        inv::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn inv_e2() {
        inv::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn inv_e4() {
        inv::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn inv_e6() {
        inv::<E6, 18>(&E6_VALUES);
    }

    fn inv_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Inv: UnaryOp<T>,
    {
        let device_fn = super::inv_in_place;
        let host_fn = |x: &T| x.inverse().unwrap_or(T::ZERO);
        unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn inv_in_place_bf() {
        inv_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn inv_in_place_e2() {
        inv_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn inv_in_place_e4() {
        inv_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn inv_in_place_e6() {
        inv_in_place::<E6, 18>(&E6_VALUES);
    }

    fn neg<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Neg: UnaryOp<T>,
    {
        let device_fn = super::neg;
        let host_fn = |x: &T| *x.clone().negate();
        unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn neg_bf() {
        neg::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn neg_e2() {
        neg::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn neg_e4() {
        neg::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn neg_e6() {
        neg::<E6, 18>(&E6_VALUES);
    }

    fn neg_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Neg: UnaryOp<T>,
    {
        let device_fn = super::neg_in_place;
        let host_fn = |x: &T| *x.clone().negate();
        unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn neg_in_place_bf() {
        neg_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn neg_in_place_e2() {
        neg_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn neg_in_place_e4() {
        neg_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn neg_in_place_e6() {
        neg_in_place::<E6, 18>(&E6_VALUES);
    }

    fn sqr<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Sqr: UnaryOp<T>,
    {
        let device_fn = super::sqr;
        let host_fn = |x: &T| *x.clone().square();
        unary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn sqr_bf() {
        sqr::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn sqr_e2() {
        sqr::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn sqr_e4() {
        sqr::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn sqr_e6() {
        sqr::<E6, 18>(&E6_VALUES);
    }

    fn sqr_in_place<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Sqr: UnaryOp<T>,
    {
        let device_fn = super::sqr_in_place;
        let host_fn = |x: &T| *x.clone().square();
        unary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn sqr_in_place_bf() {
        sqr_in_place::<BF, 20>(&BF_VALUES);
    }

    #[test]
    fn sqr_in_place_e2() {
        sqr_in_place::<E2, 19>(&E2_VALUES);
    }

    #[test]
    fn sqr_in_place_e4() {
        sqr_in_place::<E4, 18>(&E4_VALUES);
    }

    #[test]
    fn sqr_in_place_e6() {
        sqr_in_place::<E6, 18>(&E6_VALUES);
    }

    fn add<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Add: BinaryOp<T, T, T>,
    {
        let device_fn = super::add;
        let host_fn = |x: &T, y: &T| *x.clone().add_assign(y);
        binary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn add_bf() {
        add::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn add_e2() {
        add::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn add_e4() {
        add::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn add_e6() {
        add::<E6, 8>(&E6_VALUES);
    }

    fn add_into_x<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Add: BinaryOp<T, T, T>,
    {
        let device_fn = super::add_into_x;
        let host_fn = |x: &T, y: &T| *x.clone().add_assign(y);
        binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn add_into_x_bf() {
        add_into_x::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn add_into_x_e2() {
        add_into_x::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn add_into_x_e4() {
        add_into_x::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn add_into_x_e6() {
        add_into_x::<E6, 8>(&E6_VALUES);
    }

    fn add_into_y<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Add: BinaryOp<T, T, T>,
    {
        let device_fn = |y: &mut DeviceSlice<T>, x: &DeviceSlice<T>, stream: &CudaStream| {
            super::add_into_y(x, y, stream)
        };
        let host_fn = |y: &T, x: &T| *x.clone().add_assign(y);
        binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn add_into_y_bf() {
        add_into_y::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn add_into_y_e2() {
        add_into_y::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn add_into_y_e4() {
        add_into_y::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn add_into_y_e6() {
        add_into_y::<E6, 8>(&E6_VALUES);
    }

    fn mul<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Mul: BinaryOp<T, T, T>,
    {
        let device_fn = super::mul;
        let host_fn = |x: &T, y: &T| *x.clone().mul_assign(y);
        binary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn mul_bf() {
        mul::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn mul_e2() {
        mul::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn mul_e4() {
        mul::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn mul_e6() {
        mul::<E6, 8>(&E6_VALUES);
    }

    fn mul_into_x<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Mul: BinaryOp<T, T, T>,
    {
        let device_fn = super::mul_into_x;
        let host_fn = |x: &T, y: &T| *x.clone().mul_assign(y);
        binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn mul_into_x_bf() {
        mul_into_x::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn mul_into_x_e2() {
        mul_into_x::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn mul_into_x_e4() {
        mul_into_x::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn mul_into_x_e6() {
        mul_into_x::<E6, 8>(&E6_VALUES);
    }

    fn mul_into_y<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Mul: BinaryOp<T, T, T>,
    {
        let device_fn = |y: &mut DeviceSlice<T>, x: &DeviceSlice<T>, stream: &CudaStream| {
            super::mul_into_y(x, y, stream)
        };
        let host_fn = |y: &T, x: &T| *x.clone().mul_assign(y);
        binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn mul_into_y_bf() {
        mul_into_y::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn mul_into_y_e2() {
        mul_into_y::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn mul_into_y_e4() {
        mul_into_y::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn mul_into_y_e6() {
        mul_into_y::<E6, 8>(&E6_VALUES);
    }

    fn sub<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Sub: BinaryOp<T, T, T>,
    {
        let device_fn = super::sub;
        let host_fn = |x: &T, y: &T| *x.clone().sub_assign(y);
        binary_op_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn sub_bf() {
        sub::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn sub_e2() {
        sub::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn sub_e4() {
        sub::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn sub_e6() {
        sub::<E6, 8>(&E6_VALUES);
    }

    fn sub_into_x<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Sub: BinaryOp<T, T, T>,
    {
        let device_fn = super::sub_into_x;
        let host_fn = |x: &T, y: &T| *x.clone().sub_assign(y);
        binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn sub_into_x_bf() {
        sub_into_x::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn sub_into_x_e2() {
        sub_into_x::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn sub_into_x_e4() {
        sub_into_x::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn sub_into_x_e6() {
        sub_into_x::<E6, 8>(&E6_VALUES);
    }

    fn sub_into_y<T: Field, const LOG_N: u32>(additional_values: &[T])
    where
        Sub: BinaryOp<T, T, T>,
    {
        let device_fn = |y: &mut DeviceSlice<T>, x: &DeviceSlice<T>, stream: &CudaStream| {
            super::sub_into_y(x, y, stream)
        };
        let host_fn = |y: &T, x: &T| *x.clone().sub_assign(y);
        binary_op_in_place_test::<T, LOG_N>(device_fn, host_fn, additional_values);
    }

    #[test]
    fn sub_into_y_bf() {
        sub_into_y::<BF, 10>(&BF_VALUES);
    }

    #[test]
    fn sub_into_y_e2() {
        sub_into_y::<E2, 9>(&E2_VALUES);
    }

    #[test]
    fn sub_into_y_e4() {
        sub_into_y::<E4, 8>(&E4_VALUES);
    }

    #[test]
    fn sub_into_y_e6() {
        sub_into_y::<E6, 8>(&E6_VALUES);
    }
    // #[test]
    // fn sub() {
    //     let device_fn = super::sub;
    //     let host_fn = |x: &BF, y: &BF| *x.clone().sub_assign(y);
    //     binary_op_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn sub_into_x() {
    //     let device_fn = super::sub_into_x;
    //     let host_fn = |x: &BF, y: &BF| *x.clone().sub_assign(y);
    //     binary_op_in_place_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn sub_into_y() {
    //     let device_fn = |y: &mut DeviceSlice<BF>, x: &DeviceSlice<BF>, stream: &CudaStream| {
    //         super::sub_into_y(x, y, stream)
    //     };
    //     let host_fn = |y: &BF, x: &BF| *x.clone().sub_assign(y);
    //     binary_op_in_place_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn pow() {
    //     let device_fn = super::pow;
    //     let host_fn = |x: &BF, power: u32| x.clone().pow(power);
    //     for power in [0, 1, 42, 255, 256] {
    //         parametrized_unary_op_test(power, device_fn, host_fn);
    //     }
    // }
    //
    // #[test]
    // fn pow_in_place() {
    //     let device_fn = super::pow_in_place;
    //     let host_fn = |x: &BF, power: u32| x.clone().pow(power);
    //     for power in [0, 1, 42, 255, 256] {
    //         parametrized_unary_op_in_place_test(power, device_fn, host_fn);
    //     }
    // }

    // #[test]
    // fn mul_add() {
    //     let device_fn = super::mul_add;
    //     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).add_assign(z);
    //     ternary_op_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn mul_add_into_x() {
    //     let device_fn = super::mul_add_into_x;
    //     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).add_assign(z);
    //     ternary_op_in_place_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn mul_add_into_y() {
    //     let device_fn =
    //         |y: &mut DeviceSlice<BF>,
    //          x: &DeviceSlice<BF>,
    //          z: &DeviceSlice<BF>,
    //          stream: &CudaStream| super::mul_add_into_y(x, y, z, stream);
    //     let host_fn = |y: &BF, x: &BF, z: &BF| *x.clone().mul_assign(y).add_assign(z);
    //     ternary_op_in_place_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn mul_add_into_z() {
    //     let device_fn =
    //         |z: &mut DeviceSlice<BF>,
    //          x: &DeviceSlice<BF>,
    //          y: &DeviceSlice<BF>,
    //          stream: &CudaStream| super::mul_add_into_z(x, y, z, stream);
    //     let host_fn = |z: &BF, x: &BF, y: &BF| *x.clone().mul_assign(y).add_assign(z);
    //     ternary_op_in_place_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn mul_sub() {
    //     let device_fn = super::mul_sub;
    //     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).sub_assign(z);
    //     ternary_op_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn mul_sub_into_x() {
    //     let device_fn = super::mul_sub_into_x;
    //     let host_fn = |x: &BF, y: &BF, z: &BF| *x.clone().mul_assign(y).sub_assign(z);
    //     ternary_op_in_place_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn mul_sub_into_y() {
    //     let device_fn =
    //         |y: &mut DeviceSlice<BF>,
    //          x: &DeviceSlice<BF>,
    //          z: &DeviceSlice<BF>,
    //          stream: &CudaStream| super::mul_sub_into_y(x, y, z, stream);
    //     let host_fn = |y: &BF, x: &BF, z: &BF| *x.clone().mul_assign(y).sub_assign(z);
    //     ternary_op_in_place_test(device_fn, host_fn);
    // }
    //
    // #[test]
    // fn mul_sub_into_z() {
    //     let device_fn =
    //         |z: &mut DeviceSlice<BF>,
    //          x: &DeviceSlice<BF>,
    //          y: &DeviceSlice<BF>,
    //          stream: &CudaStream| super::mul_sub_into_z(x, y, z, stream);
    //     let host_fn = |z: &BF, x: &BF, y: &BF| *x.clone().mul_assign(y).sub_assign(z);
    //     ternary_op_in_place_test(device_fn, host_fn);
    // }
}
