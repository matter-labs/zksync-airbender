use std::ptr::{null, null_mut};

use era_cudart::paste::paste;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaError_t, cudaStream_t};

use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceVectorChunkImpl, PtrAndStride,
};
use crate::primitives::field::{BF, E4};

#[derive(Copy, Clone)]
pub(crate) enum ReduceOperation {
    Sum,
    #[allow(dead_code)] // only constructed in tests; kept for the CUB API surface.
    Product,
}

type ReduceFunction<T> = unsafe extern "C" fn(
    d_temp_storage: *mut u8,
    temp_storage_bytes: &mut usize,
    d_in: *const T,
    d_out: *mut T,
    num_items: i32,
    stream: cudaStream_t,
) -> cudaError_t;

type SegmentedReduceFunction<T> = unsafe extern "C" fn(
    d_temp_storage: *mut u8,
    temp_storage_bytes: &mut usize,
    d_in: PtrAndStride<T>,
    d_out: *mut T,
    num_segments: i32,
    num_items: i32,
    stream: cudaStream_t,
) -> cudaError_t;

pub(crate) trait Reduce: Sized {
    fn get_reduce_function(operation: ReduceOperation) -> ReduceFunction<Self>;

    fn get_segmented_reduce_function(operation: ReduceOperation) -> SegmentedReduceFunction<Self>;

    fn get_reduce_temp_storage_bytes(
        operation: ReduceOperation,
        num_items: i32,
    ) -> CudaResult<usize> {
        let mut temp_storage_bytes = 0;
        let function = Self::get_reduce_function(operation);
        unsafe {
            function(
                null_mut(),
                &mut temp_storage_bytes,
                null(),
                null_mut(),
                num_items,
                null_mut(),
            )
            .wrap_value(temp_storage_bytes)
        }
    }

    fn get_batch_reduce_temp_storage_bytes(
        operation: ReduceOperation,
        batch_size: i32,
        num_items: i32,
    ) -> CudaResult<usize> {
        let mut temp_storage_bytes = 0;
        let function = Self::get_segmented_reduce_function(operation);
        unsafe {
            function(
                null_mut(),
                &mut temp_storage_bytes,
                PtrAndStride::new(null(), num_items as usize),
                null_mut(),
                batch_size,
                num_items,
                null_mut(),
            )
            .wrap_value(temp_storage_bytes)
        }
    }

    fn reduce(
        operation: ReduceOperation,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_in: &(impl DeviceVectorChunkImpl<Self> + ?Sized),
        d_out: &mut DeviceVariable<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let mut temp_storage_bytes = d_temp_storage.len();
        assert!(d_in.rows() <= i32::MAX as usize);
        let num_items = d_in.rows() as i32;
        let function = Self::get_reduce_function(operation);
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_in.as_ptr(),
                d_out.as_mut_ptr() as *mut _,
                num_items,
                stream.into(),
            )
            .wrap()
        }
    }

    fn batch_reduce(
        operation: ReduceOperation,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_in: &(impl DeviceMatrixChunkImpl<Self> + ?Sized),
        d_out: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let mut temp_storage_bytes = d_temp_storage.len();
        assert_eq!(d_in.cols(), d_out.len());
        let num_segments = d_in.cols() as i32;
        let num_items = d_in.rows() as i32;
        let function = Self::get_segmented_reduce_function(operation);
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_in.as_ptr_and_stride(),
                d_out.as_mut_ptr() as *mut _,
                num_segments,
                num_items,
                stream.into(),
            )
            .wrap()
        }
    }
}

pub(crate) fn get_reduce_temp_storage_bytes<T: Reduce>(
    operation: ReduceOperation,
    num_items: i32,
) -> CudaResult<usize> {
    T::get_reduce_temp_storage_bytes(operation, num_items)
}

pub(crate) fn reduce<T: Reduce>(
    operation: ReduceOperation,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_in: &(impl DeviceVectorChunkImpl<T> + ?Sized),
    d_out: &mut DeviceVariable<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::reduce(operation, d_temp_storage, d_in, d_out, stream)
}

pub(crate) fn get_batch_reduce_temp_storage_bytes<T: Reduce>(
    operation: ReduceOperation,
    batch_size: i32,
    num_items: i32,
) -> CudaResult<usize> {
    T::get_batch_reduce_temp_storage_bytes(operation, batch_size, num_items)
}

pub(crate) fn batch_reduce<T: Reduce>(
    operation: ReduceOperation,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_in: &(impl DeviceMatrixChunkImpl<T> + ?Sized),
    d_out: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::batch_reduce(operation, d_temp_storage, d_in, d_out, stream)
}

macro_rules! reduce_fns {
    ($function:ident, $type:ty) => {
        paste! {
            ::era_cudart_sys::cuda_fn_and_stub! {
                fn [<ab_reduce_ $function _ $type:lower>](
                    d_temp_storage: *mut u8,
                    temp_storage_bytes: &mut usize,
                    d_in: *const $type,
                    d_out: *mut $type,
                    num_items: i32,
                    stream: cudaStream_t,
                ) -> cudaError_t;
            }

            ::era_cudart_sys::cuda_fn_and_stub! {
                fn [<ab_segmented_reduce_ $function _ $type:lower>](
                    d_temp_storage: *mut u8,
                    temp_storage_bytes: &mut usize,
                    d_in: PtrAndStride<$type>,
                    d_out: *mut $type,
                    num_segments: i32,
                    num_items: i32,
                    stream: cudaStream_t,
                ) -> cudaError_t;
            }
        }
    };
}

macro_rules! reduce_impl {
    ($type:ty) => {
        paste! {
            reduce_fns!(add, $type);
            reduce_fns!(mul, $type);
            impl Reduce for $type {
                fn get_reduce_function(operation: ReduceOperation) -> ReduceFunction<Self> {
                    match operation {
                        ReduceOperation::Sum => [<ab_reduce_add_ $type:lower>],
                        ReduceOperation::Product => [<ab_reduce_mul_ $type:lower>],
                    }
                }

                fn get_segmented_reduce_function(
                    operation: ReduceOperation,
                ) -> SegmentedReduceFunction<Self> {
                    match operation {
                        ReduceOperation::Sum => [<ab_segmented_reduce_add_ $type:lower>],
                        ReduceOperation::Product => [<ab_segmented_reduce_mul_ $type:lower>],
                    }
                }
            }
        }
    };
}

reduce_impl!(BF);
reduce_impl!(E4);

#[cfg(test)]
mod tests {
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use era_cudart::stream::CudaStream;
    use field::Field;
    use itertools::Itertools;
    use rand::rng;

    use crate::ops::cub::device_reduce::{Reduce, ReduceOperation};
    use crate::primitives::device_structures::DeviceMatrix;

    type HostFunction<F> = fn(F, F) -> F;

    fn generate<F: Field>(count: usize) -> Vec<F> {
        let mut rng = rng();
        (0..count)
            .map(|_| F::random_element(&mut rng))
            .collect_vec()
    }

    fn reduce<F: Field + Reduce>(
        operation: ReduceOperation,
        init: F,
        host_function: HostFunction<F>,
    ) {
        const NUM_ITEMS: usize = 1 << 16;
        let temp_storage_bytes =
            super::get_reduce_temp_storage_bytes::<F>(operation, NUM_ITEMS as i32).unwrap();
        let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
        let h_in = generate(NUM_ITEMS);
        let mut h_out = [F::default()];
        let mut d_in = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
        let mut d_out = DeviceAllocation::alloc(1).unwrap();
        let stream = CudaStream::default();
        memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
        super::reduce(
            operation,
            &mut d_temp_storage,
            &d_in,
            &mut d_out[0],
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut h_out, &d_out, &stream).unwrap();
        stream.synchronize().unwrap();
        let result = h_in.into_iter().fold(init, host_function);
        assert_eq!(result, h_out[0]);
    }

    fn batch_reduce<F: Field + Reduce>(
        operation: ReduceOperation,
        init: F,
        host_function: HostFunction<F>,
    ) {
        const BATCH_SIZE: usize = 1 << 8;
        const NUM_ITEMS: usize = 1 << 8;
        let temp_storage_bytes = super::get_batch_reduce_temp_storage_bytes::<F>(
            operation,
            BATCH_SIZE as i32,
            NUM_ITEMS as i32,
        )
        .unwrap();
        let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
        let h_in = generate(NUM_ITEMS * BATCH_SIZE);
        let mut h_out = [F::default(); BATCH_SIZE];
        let mut d_in = DeviceAllocation::alloc(NUM_ITEMS * BATCH_SIZE).unwrap();
        let mut d_out = DeviceAllocation::alloc(BATCH_SIZE).unwrap();
        let stream = CudaStream::default();
        memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
        let d_in_matrix = DeviceMatrix::new(&d_in, NUM_ITEMS);
        super::batch_reduce(
            operation,
            &mut d_temp_storage,
            &d_in_matrix,
            &mut d_out,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut h_out, &d_out, &stream).unwrap();
        stream.synchronize().unwrap();
        let result = h_in
            .into_iter()
            .chunks(NUM_ITEMS)
            .into_iter()
            .map(|c| c.fold(init, host_function))
            .collect_vec();
        assert!(result
            .into_iter()
            .zip(h_out.into_iter())
            .all(|(a, b)| a == b));
    }

    type TestFunction<F> = fn(ReduceOperation, F, HostFunction<F>);

    fn test_sum<F: Field>(test_function: TestFunction<F>) {
        test_function(ReduceOperation::Sum, F::ZERO, |state, x| {
            let mut result = state;
            result.add_assign(&x);
            result
        })
    }

    fn test_product<F: Field>(test_function: TestFunction<F>) {
        test_function(ReduceOperation::Product, F::ONE, |state, x| {
            let mut result = state;
            result.mul_assign(&x);
            result
        })
    }

    #[test]
    fn sum_bf() {
        test_sum(reduce::<super::BF>)
    }

    #[test]
    fn batch_sum_bf() {
        test_sum(batch_reduce::<super::BF>)
    }

    #[test]
    fn product_bf() {
        test_product(reduce::<super::BF>)
    }

    #[test]
    fn batch_product_bf() {
        test_product(batch_reduce::<super::BF>)
    }

    #[test]
    fn sum_e4() {
        test_sum(reduce::<super::E4>)
    }

    #[test]
    fn batch_sum_e4() {
        test_sum(batch_reduce::<super::E4>)
    }

    #[test]
    fn product_e4() {
        test_product(reduce::<super::E4>)
    }

    #[test]
    fn batch_product_e4() {
        test_product(batch_reduce::<super::E4>)
    }
}
