use std::ptr::null_mut;

use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaError_t, cudaStream_t, cuda_fn_and_stub};

use crate::field::BaseField;

cuda_fn_and_stub! {
    fn ab_encode_u32(
        d_temp_storage: *mut u8,
        temp_storage_bytes: &mut usize,
        d_in: *const u32,
        d_unique_out: *mut u32,
        d_counts_out: *mut u32,
        d_num_runs_out: *mut u32,
        num_items: i32,
        stream: cudaStream_t,
    ) -> cudaError_t;
}

pub type EncodeFunction<T> = unsafe extern "C" fn(
    d_temp_storage: *mut u8,
    temp_storage_bytes: &mut usize,
    d_in: *const T,
    d_unique_out: *mut T,
    d_counts_out: *mut u32,
    d_num_runs_out: *mut u32,
    num_items: i32,
    stream: cudaStream_t,
) -> cudaError_t;

pub trait Encode: Sized {
    fn get_function() -> EncodeFunction<Self>;

    fn get_encode_temp_storage_bytes(num_items: i32) -> CudaResult<usize> {
        let d_temp_storage = DeviceSlice::empty_mut();
        let mut temp_storage_bytes = 0;
        let d_in = DeviceSlice::empty();
        let d_unique_out = DeviceSlice::empty_mut();
        let d_counts_out = DeviceSlice::empty_mut();
        let d_num_runs_out = DeviceSlice::empty_mut();
        let function = Self::get_function();
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_in.as_ptr(),
                d_unique_out.as_mut_ptr(),
                d_counts_out.as_mut_ptr(),
                d_num_runs_out.as_mut_ptr(),
                num_items,
                null_mut(),
            )
            .wrap_value(temp_storage_bytes)
        }
    }

    fn encode(
        d_temp_storage: &mut DeviceSlice<u8>,
        d_in: &DeviceSlice<Self>,
        d_unique_out: &mut DeviceSlice<Self>,
        d_counts_out: &mut DeviceSlice<u32>,
        d_num_runs_out: &mut DeviceVariable<u32>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let mut temp_storage_bytes = d_temp_storage.len();
        assert!(d_in.len() <= i32::MAX as usize);
        let num_items = d_in.len() as i32;
        assert_eq!(d_unique_out.len(), d_counts_out.len());
        let function = Self::get_function();
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_in.as_ptr(),
                d_unique_out.as_mut_ptr(),
                d_counts_out.as_mut_ptr(),
                d_num_runs_out.as_mut_ptr(),
                num_items,
                stream.into(),
            )
            .wrap()
        }
    }
}

impl Encode for u32 {
    fn get_function() -> EncodeFunction<Self> {
        ab_encode_u32
    }
}

impl Encode for BaseField {
    fn get_function() -> EncodeFunction<Self> {
        unimplemented!()
    }

    fn encode(
        d_temp_storage: &mut DeviceSlice<u8>,
        d_in: &DeviceSlice<Self>,
        d_unique_out: &mut DeviceSlice<Self>,
        d_counts_out: &mut DeviceSlice<u32>,
        d_num_runs_out: &mut DeviceVariable<u32>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let d_in = unsafe { d_in.transmute() };
        let d_unique_out = unsafe { d_unique_out.transmute_mut() };
        u32::encode(
            d_temp_storage,
            d_in,
            d_unique_out,
            d_counts_out,
            d_num_runs_out,
            stream,
        )
    }
}

pub fn get_encode_temp_storage_bytes<T: Encode>(num_items: i32) -> CudaResult<usize> {
    T::get_encode_temp_storage_bytes(num_items)
}

pub fn encode<T: Encode>(
    d_temp_storage: &mut DeviceSlice<u8>,
    d_in: &DeviceSlice<T>,
    d_unique_out: &mut DeviceSlice<T>,
    d_counts_out: &mut DeviceSlice<u32>,
    d_num_runs_out: &mut DeviceVariable<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::encode(
        d_temp_storage,
        d_in,
        d_unique_out,
        d_counts_out,
        d_num_runs_out,
        stream,
    )
}

#[cfg(test)]
mod tests {
    use rand::rng;
    use std::fmt::Debug;

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use era_cudart::stream::CudaStream;
    use itertools::Itertools;
    use rand::distr::Uniform;
    use rand::Rng;

    fn encode<T>()
    where
        T: super::Encode + Default + Copy + Clone + Ord + Eq + Debug + From<u32>,
    {
        const NUM_ITEMS: usize = 1 << 16;
        const RANGE_MAX: u32 = 2;
        let temp_storage_bytes =
            super::get_encode_temp_storage_bytes::<T>(NUM_ITEMS as i32).unwrap();
        let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
        let h_in = rng()
            .sample_iter(Uniform::new(0, RANGE_MAX).unwrap())
            .map(|x| x.into())
            .take(NUM_ITEMS)
            .collect_vec();
        let mut h_unique_out = vec![T::default(); NUM_ITEMS];
        let mut h_counts_out = vec![0u32; NUM_ITEMS];
        let mut h_num_runs_out = [0u32];
        let mut d_in = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
        let mut d_unique_out = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
        let mut d_counts_out = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
        let mut d_num_runs_out = DeviceAllocation::alloc(1).unwrap();
        let stream = CudaStream::default();
        memory_copy_async(&mut d_in, &h_in, &stream).unwrap();
        super::encode(
            &mut d_temp_storage,
            &d_in,
            &mut d_unique_out,
            &mut d_counts_out,
            &mut d_num_runs_out[0],
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut h_unique_out, &d_unique_out, &stream).unwrap();
        memory_copy_async(&mut h_counts_out, &d_counts_out, &stream).unwrap();
        memory_copy_async(&mut h_num_runs_out, &d_num_runs_out, &stream).unwrap();
        stream.synchronize().unwrap();
        let mut run_index = 0usize;
        let mut current_value = h_in[0];
        let mut current_count = 0;
        for x in h_in {
            if x == current_value {
                current_count += 1;
            } else {
                assert_eq!(current_value, h_unique_out[run_index]);
                assert_eq!(current_count, h_counts_out[run_index]);
                run_index += 1;
                current_value = x;
                current_count = 1;
            }
        }
        assert_eq!(current_value, h_unique_out[run_index]);
        assert_eq!(current_count, h_counts_out[run_index]);
        assert_eq!(run_index + 1, h_num_runs_out[0] as usize);
    }

    #[test]
    fn encode_u32() {
        encode::<u32>();
    }
}
