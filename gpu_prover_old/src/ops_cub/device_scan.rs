use std::ptr::null_mut;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::paste::paste;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::{CudaStream, CudaStreamCreateFlags, CudaStreamWaitEventFlags};
use era_cudart_sys::{cudaError_t, cudaStream_t};

use crate::field::{BaseField, Ext4Field};

type BF = BaseField;
type E4 = Ext4Field;

macro_rules! scan_fn {
    ($i_or_e:ident, $function:ident, $type:ty) => {
        paste! {
            ::era_cudart_sys::cuda_fn_and_stub! {
                fn [<ab_scan_ $i_or_e _ $function _ $type:lower>](
                    d_temp_storage: *mut u8,
                    temp_storage_bytes: &mut usize,
                    d_in: *const $type,
                    d_out: *mut $type,
                    num_items: i32,
                    stream: cudaStream_t,
                ) -> cudaError_t;
            }
        }
    };
}

macro_rules! scan_fns {
    ($type:ty) => {
        scan_fn!(e, add, $type);
        scan_fn!(i, add, $type);
        scan_fn!(e, mul, $type);
        scan_fn!(i, mul, $type);
    };
}

#[derive(Copy, Clone)]
pub enum ScanOperation {
    Sum,
    Product,
}

type ScanFunction<T> = unsafe extern "C" fn(
    d_temp_storage: *mut u8,
    temp_storage_bytes: &mut usize,
    d_in: *const T,
    d_out: *mut T,
    num_items: i32,
    stream: cudaStream_t,
) -> cudaError_t;

pub trait Scan: Sized {
    fn get_function(operation: ScanOperation, inclusive: bool) -> ScanFunction<Self>;

    fn get_scan_temp_storage_bytes(
        operation: ScanOperation,
        inclusive: bool,
        num_items: i32,
    ) -> CudaResult<usize> {
        let d_temp_storage = DeviceSlice::empty_mut();
        let mut temp_storage_bytes = 0;
        let d_in = DeviceSlice::empty();
        let d_out = DeviceSlice::empty_mut();
        let function = Self::get_function(operation, inclusive);
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_in.as_ptr(),
                d_out.as_mut_ptr(),
                num_items,
                null_mut(),
            )
            .wrap_value(temp_storage_bytes)
        }
    }

    fn get_batch_scan_temp_storage_bytes(
        operation: ScanOperation,
        inclusive: bool,
        batch_size: i32,
        num_items: i32,
    ) -> CudaResult<usize> {
        get_scan_temp_storage_bytes::<Self>(operation, inclusive, num_items)
            .map(|x| x * batch_size as usize)
    }

    fn scan(
        operation: ScanOperation,
        inclusive: bool,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_in: &DeviceSlice<Self>,
        d_out: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let mut temp_storage_bytes = d_temp_storage.len();
        assert_eq!(d_in.len(), d_out.len());
        assert!(d_out.len() <= i32::MAX as usize);
        let num_items = d_out.len() as i32;
        let function = Self::get_function(operation, inclusive);
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_in.as_ptr(),
                d_out.as_mut_ptr(),
                num_items,
                stream.into(),
            )
            .wrap()
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn batch_scan(
        operation: ScanOperation,
        inclusive: bool,
        batch_size: i32,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_in: &DeviceSlice<Self>,
        d_out: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let num_items = (d_in.len() / batch_size as usize) as i32;
        Self::batch_chunk_scan(
            operation,
            inclusive,
            batch_size,
            0,
            num_items,
            d_temp_storage,
            d_in,
            d_out,
            stream,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn batch_chunk_scan(
        operation: ScanOperation,
        inclusive: bool,
        batch_size: i32,
        chunk_offset: i32,
        num_items: i32,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_in: &DeviceSlice<Self>,
        d_out: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        assert_eq!(d_in.len() % batch_size as usize, 0);
        assert_eq!(d_in.len(), d_out.len());
        let temp_storage_stride = d_temp_storage.len() / batch_size as usize;
        let data_stride = d_in.len() / batch_size as usize;
        assert!(chunk_offset + num_items <= data_stride as i32);
        let parent_ready = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        parent_ready.record(stream)?;
        for i in 0..batch_size as usize {
            let child_stream = CudaStream::create_with_flags(CudaStreamCreateFlags::NON_BLOCKING)?;
            child_stream.wait_event(&parent_ready, CudaStreamWaitEventFlags::DEFAULT)?;
            let d_temp_storage =
                &mut d_temp_storage[i * temp_storage_stride..(i + 1) * temp_storage_stride];
            let data_offset = i * data_stride + chunk_offset as usize;
            let d_in = &d_in[data_offset..data_offset + num_items as usize];
            let d_out = &mut d_out[data_offset..data_offset + num_items as usize];
            scan(
                operation,
                inclusive,
                d_temp_storage,
                d_in,
                d_out,
                &child_stream,
            )?;
            let child_finished =
                CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
            child_finished.record(&child_stream)?;
            stream.wait_event(&child_finished, CudaStreamWaitEventFlags::DEFAULT)?;
            child_finished.destroy()?;
            child_stream.destroy()?;
        }
        parent_ready.destroy()?;
        Ok(())
    }

    fn scan_in_place(
        operation: ScanOperation,
        inclusive: bool,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_values: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let mut temp_storage_bytes = d_temp_storage.len();
        assert!(d_values.len() <= i32::MAX as usize);
        let num_items = d_values.len() as i32;
        let function = Self::get_function(operation, inclusive);
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_values.as_ptr(),
                d_values.as_mut_ptr(),
                num_items,
                stream.into(),
            )
            .wrap()
        }
    }

    fn batch_scan_in_place(
        operation: ScanOperation,
        inclusive: bool,
        batch_size: i32,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_values: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let num_items = (d_values.len() / batch_size as usize) as i32;
        Self::batch_chunk_scan_in_place(
            operation,
            inclusive,
            batch_size,
            0,
            num_items,
            d_temp_storage,
            d_values,
            stream,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn batch_chunk_scan_in_place(
        operation: ScanOperation,
        inclusive: bool,
        batch_size: i32,
        chunk_offset: i32,
        num_items: i32,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_values: &mut DeviceSlice<Self>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        assert_eq!(d_values.len() % batch_size as usize, 0);
        let temp_storage_stride = d_temp_storage.len() / batch_size as usize;
        let data_stride = d_values.len() / batch_size as usize;
        assert!(chunk_offset + num_items <= data_stride as i32);
        let parent_ready = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        parent_ready.record(stream)?;
        for i in 0..batch_size as usize {
            let child_stream = CudaStream::create_with_flags(CudaStreamCreateFlags::NON_BLOCKING)?;
            child_stream.wait_event(&parent_ready, CudaStreamWaitEventFlags::DEFAULT)?;
            let d_temp_storage =
                &mut d_temp_storage[i * temp_storage_stride..(i + 1) * temp_storage_stride];
            let data_offset = i * data_stride + chunk_offset as usize;
            let d_values = &mut d_values[data_offset..data_offset + num_items as usize];
            scan_in_place(
                operation,
                inclusive,
                d_temp_storage,
                d_values,
                &child_stream,
            )?;
            let child_finished =
                CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
            child_finished.record(&child_stream)?;
            stream.wait_event(&child_finished, CudaStreamWaitEventFlags::DEFAULT)?;
            child_finished.destroy()?;
            child_stream.destroy()?;
        }
        parent_ready.destroy()?;
        Ok(())
    }
}

scan_fn!(e, add, u32);
scan_fn!(i, add, u32);

impl Scan for u32 {
    fn get_function(operation: ScanOperation, inclusive: bool) -> ScanFunction<Self> {
        match (operation, inclusive) {
            (ScanOperation::Sum, false) => ab_scan_e_add_u32,
            (ScanOperation::Sum, true) => ab_scan_i_add_u32,
            (ScanOperation::Product, _) => unimplemented!(),
        }
    }
}

macro_rules! scan_impl {
    ($type:ty) => {
        paste! {
            scan_fns!($type);
            impl Scan for $type {
                fn get_function(
                    operation: ScanOperation,
                    inclusive: bool,
                ) -> ScanFunction<Self> {
                    match (operation, inclusive) {
                        (ScanOperation::Sum, false) => [<ab_scan_e_add_ $type:lower>],
                        (ScanOperation::Sum, true) => [<ab_scan_i_add_ $type:lower>],
                        (ScanOperation::Product, false) => [<ab_scan_e_mul_ $type:lower>],
                        (ScanOperation::Product, true) => [<ab_scan_i_mul_ $type:lower>],
                    }
                }
            }
        }
    };
}

scan_impl!(BF);
scan_impl!(E4);

pub fn get_scan_temp_storage_bytes<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    num_items: i32,
) -> CudaResult<usize> {
    T::get_scan_temp_storage_bytes(operation, inclusive, num_items)
}

pub fn get_batch_scan_temp_storage_bytes<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    batch_size: i32,
    num_items: i32,
) -> CudaResult<usize> {
    T::get_batch_scan_temp_storage_bytes(operation, inclusive, batch_size, num_items)
}

pub fn scan<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_in: &DeviceSlice<T>,
    d_out: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::scan(operation, inclusive, d_temp_storage, d_in, d_out, stream)
}

#[allow(clippy::too_many_arguments)]
pub fn batch_scan<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    batch_size: i32,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_in: &DeviceSlice<T>,
    d_out: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::batch_scan(
        operation,
        inclusive,
        batch_size,
        d_temp_storage,
        d_in,
        d_out,
        stream,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn batch_chunk_scan<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    batch_size: i32,
    chunk_offset: i32,
    num_items: i32,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_in: &DeviceSlice<T>,
    d_out: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::batch_chunk_scan(
        operation,
        inclusive,
        batch_size,
        chunk_offset,
        num_items,
        d_temp_storage,
        d_in,
        d_out,
        stream,
    )
}

pub fn scan_in_place<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_values: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::scan_in_place(operation, inclusive, d_temp_storage, d_values, stream)
}

pub fn batch_scan_in_place<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    batch_size: i32,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_values: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::batch_scan_in_place(
        operation,
        inclusive,
        batch_size,
        d_temp_storage,
        d_values,
        stream,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn batch_chunk_scan_in_place<T: Scan>(
    operation: ScanOperation,
    inclusive: bool,
    batch_size: i32,
    chunk_offset: i32,
    num_items: i32,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_values: &mut DeviceSlice<T>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::batch_chunk_scan_in_place(
        operation,
        inclusive,
        batch_size,
        chunk_offset,
        num_items,
        d_temp_storage,
        d_values,
        stream,
    )
}

#[cfg(test)]
mod tests {
    use std::convert::identity;

    use crate::ops_cub::device_scan::{get_scan_temp_storage_bytes, Scan};
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use era_cudart::stream::CudaStream;
    use field::Field;
    use itertools::Itertools;
    use rand::distr::Uniform;
    use rand::{rng, Rng};

    use super::ScanOperation;
    use super::BF;

    trait ScanTest: Scan + Default + Copy + Eq {
        fn get_initial_state(operation: ScanOperation) -> Self;
        fn scan_operation(operation: ScanOperation, a: Self, b: Self) -> Self;

        fn verify(operation: ScanOperation, inclusive: bool, h_in: Vec<Self>, h_out: Vec<Self>) {
            let initial_state = Self::get_initial_state(operation);
            let state_fn = |state: &mut Self, x| {
                let current = *state;
                let next = Self::scan_operation(operation, current, x);
                *state = next;
                Some(if inclusive { next } else { current })
            };
            let h_in = h_in.into_iter().scan(initial_state, state_fn).collect_vec();
            assert!(h_in.into_iter().zip(h_out.into_iter()).all(|(x, y)| x == y));
        }

        fn scan(operation: ScanOperation, inclusive: bool, convert: fn(u32) -> Self) {
            const NUM_ITEMS: usize = 1 << 16;
            const RANGE_MAX: u32 = 1 << 16;
            let temp_storage_bytes =
                get_scan_temp_storage_bytes::<Self>(operation, inclusive, NUM_ITEMS as i32)
                    .unwrap();
            let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
            let h_in = rng()
                .sample_iter(Uniform::new(0, RANGE_MAX).unwrap())
                .map(convert)
                .take(NUM_ITEMS)
                .collect_vec();
            let mut h_out = vec![Self::default(); NUM_ITEMS];
            let mut d_in = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
            let mut d_out = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
            let stream = CudaStream::default();
            memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
            super::scan(
                operation,
                inclusive,
                &mut d_temp_storage,
                &d_in,
                &mut d_out,
                &stream,
            )
            .unwrap();
            memory_copy_async(&mut h_out, &d_out, &stream).unwrap();
            stream.synchronize().unwrap();
            Self::verify(operation, inclusive, h_in, h_out);
        }

        fn batch_scan(operation: ScanOperation, inclusive: bool, convert: fn(u32) -> Self) {
            const BATCH_SIZE: usize = 1 << 8;
            const NUM_ITEMS: usize = 1 << 8;
            const RANGE_MAX: u32 = 1 << 16;
            let temp_storage_bytes = super::get_batch_scan_temp_storage_bytes::<Self>(
                operation,
                inclusive,
                BATCH_SIZE as i32,
                NUM_ITEMS as i32,
            )
            .unwrap();
            let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
            let h_in = rng()
                .sample_iter(Uniform::new(0, RANGE_MAX).unwrap())
                .map(convert)
                .take(NUM_ITEMS * BATCH_SIZE)
                .collect_vec();
            let mut h_out = vec![Self::default(); NUM_ITEMS * BATCH_SIZE];
            let mut d_in = DeviceAllocation::alloc(NUM_ITEMS * BATCH_SIZE).unwrap();
            let mut d_out = DeviceAllocation::alloc(NUM_ITEMS * BATCH_SIZE).unwrap();
            let stream = CudaStream::default();
            memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
            super::batch_scan(
                operation,
                inclusive,
                BATCH_SIZE as i32,
                &mut d_temp_storage,
                &d_in,
                &mut d_out,
                &stream,
            )
            .unwrap();
            memory_copy_async(&mut h_out, &d_out, &stream).unwrap();
            stream.synchronize().unwrap();
            h_in.into_iter()
                .chunks(NUM_ITEMS)
                .into_iter()
                .zip(h_out.chunks(NUM_ITEMS))
                .for_each(|(h_in, h_out)| {
                    let h_in = h_in.collect_vec();
                    let h_out = Vec::from(h_out);
                    Self::verify(operation, inclusive, h_in, h_out);
                });
        }

        fn batch_chunk_scan(operation: ScanOperation, inclusive: bool, convert: fn(u32) -> Self) {
            const BATCH_SIZE: usize = 1 << 8;
            const NUM_ITEMS: usize = 1 << 8;
            const STRIDE: usize = NUM_ITEMS * 2;
            const RANGE_MAX: u32 = 1 << 16;
            let temp_storage_bytes = super::get_batch_scan_temp_storage_bytes::<Self>(
                operation,
                inclusive,
                BATCH_SIZE as i32,
                NUM_ITEMS as i32,
            )
            .unwrap();
            let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
            let h_in = rng()
                .sample_iter(Uniform::new(0, RANGE_MAX).unwrap())
                .map(convert)
                .take(STRIDE * BATCH_SIZE)
                .collect_vec();
            let mut h_out = vec![Self::default(); STRIDE * BATCH_SIZE];
            let mut d_in = DeviceAllocation::alloc(STRIDE * BATCH_SIZE).unwrap();
            let mut d_out = DeviceAllocation::alloc(STRIDE * BATCH_SIZE).unwrap();
            let stream = CudaStream::default();
            memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
            super::batch_chunk_scan(
                operation,
                inclusive,
                BATCH_SIZE as i32,
                NUM_ITEMS as i32,
                NUM_ITEMS as i32,
                &mut d_temp_storage,
                &d_in,
                &mut d_out,
                &stream,
            )
            .unwrap();
            memory_copy_async(&mut h_out, &d_out, &stream).unwrap();
            stream.synchronize().unwrap();
            h_in.into_iter()
                .chunks(STRIDE)
                .into_iter()
                .skip(NUM_ITEMS)
                .zip(
                    h_out
                        .into_iter()
                        .chunks(NUM_ITEMS)
                        .into_iter()
                        .skip(NUM_ITEMS),
                )
                .for_each(|(h_in, h_out)| {
                    let h_in = h_in.collect_vec();
                    let h_out = h_out.collect_vec();
                    Self::verify(operation, inclusive, h_in, h_out);
                });
        }
    }

    impl ScanTest for u32 {
        fn get_initial_state(operation: ScanOperation) -> Self {
            match operation {
                ScanOperation::Sum => 0,
                ScanOperation::Product => unimplemented!(),
            }
        }

        fn scan_operation(operation: ScanOperation, a: Self, b: Self) -> Self {
            match operation {
                ScanOperation::Sum => a + b,
                ScanOperation::Product => unimplemented!(),
            }
        }
    }

    impl ScanTest for BF {
        fn get_initial_state(operation: ScanOperation) -> Self {
            match operation {
                ScanOperation::Sum => Self::ZERO,
                ScanOperation::Product => Self::ONE,
            }
        }

        fn scan_operation(operation: ScanOperation, a: Self, b: Self) -> Self {
            match operation {
                ScanOperation::Sum => {
                    let mut result = a;
                    result.add_assign(&b);
                    result
                }
                ScanOperation::Product => {
                    let mut result = a;
                    result.mul_assign(&b);
                    result
                }
            }
        }
    }

    fn scan_u32(operation: ScanOperation, inclusive: bool) {
        <u32 as ScanTest>::scan(operation, inclusive, identity);
    }

    fn batch_scan_u32(operation: ScanOperation, inclusive: bool) {
        <u32 as ScanTest>::batch_scan(operation, inclusive, identity);
    }

    fn batch_chunk_scan_u32(operation: ScanOperation, inclusive: bool) {
        <u32 as ScanTest>::batch_chunk_scan(operation, inclusive, identity);
    }

    fn scan_bf(operation: ScanOperation, inclusive: bool) {
        <BF as ScanTest>::scan(operation, inclusive, BF::from_nonreduced_u32);
    }

    fn batch_scan_bf(operation: ScanOperation, inclusive: bool) {
        <BF as ScanTest>::batch_scan(operation, inclusive, BF::from_nonreduced_u32);
    }

    fn batch_chunk_scan_bf(operation: ScanOperation, inclusive: bool) {
        <BF as ScanTest>::batch_chunk_scan(operation, inclusive, BF::from_nonreduced_u32);
    }

    #[test]
    fn scan_e_add_u32() {
        scan_u32(ScanOperation::Sum, false);
    }

    #[test]
    fn scan_i_add_u32() {
        scan_u32(ScanOperation::Sum, true);
    }

    #[test]
    fn batch_scan_e_add_u32() {
        batch_scan_u32(ScanOperation::Sum, false);
    }

    #[test]
    fn batch_scan_i_add_u32() {
        batch_scan_u32(ScanOperation::Sum, true);
    }

    #[test]
    fn batch_chunk_scan_e_add_u32() {
        batch_chunk_scan_u32(ScanOperation::Sum, false);
    }

    #[test]
    fn batch_chunk_scan_i_add_u32() {
        batch_chunk_scan_u32(ScanOperation::Sum, true);
    }

    #[test]
    fn scan_e_add_bf() {
        scan_bf(ScanOperation::Sum, false);
    }

    #[test]
    fn scan_i_add_bf() {
        scan_bf(ScanOperation::Sum, true);
    }

    #[test]
    fn scan_e_mul_bf() {
        scan_bf(ScanOperation::Product, false);
    }

    #[test]
    fn scan_i_mul_bf() {
        scan_bf(ScanOperation::Product, true);
    }

    #[test]
    fn batch_scan_e_add_bf() {
        batch_scan_bf(ScanOperation::Sum, false);
    }

    #[test]
    fn batch_scan_i_add_bf() {
        batch_scan_bf(ScanOperation::Sum, true);
    }

    #[test]
    fn batch_scan_e_mul_bf() {
        batch_scan_bf(ScanOperation::Product, false);
    }

    #[test]
    fn batch_scan_i_mul_bf() {
        batch_scan_bf(ScanOperation::Product, true);
    }

    #[test]
    fn batch_chunk_scan_e_add_bf() {
        batch_chunk_scan_bf(ScanOperation::Sum, false);
    }

    #[test]
    fn batch_chunk_scan_i_add_bf() {
        batch_chunk_scan_bf(ScanOperation::Sum, true);
    }

    #[test]
    fn batch_chunk_scan_e_mul_bf() {
        batch_chunk_scan_bf(ScanOperation::Product, false);
    }

    #[test]
    fn batch_chunk_scan_i_mul_bf() {
        batch_chunk_scan_bf(ScanOperation::Product, true);
    }
}
