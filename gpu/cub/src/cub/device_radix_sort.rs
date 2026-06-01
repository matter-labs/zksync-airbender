use std::ptr::{null, null_mut};

use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaError_t, cudaStream_t, cuda_fn_and_stub};
use gpu_core::primitives::field::BF;

cuda_fn_and_stub! {
    fn ab_sort_keys_a_u32(
        d_temp_storage: *mut u8,
        temp_storage_bytes: &mut usize,
        d_keys_in: *const u32,
        d_keys_out: *mut u32,
        num_items: u32,
        begin_bit: i32,
        end_bit: i32,
        stream: cudaStream_t,
    ) -> cudaError_t;
}

cuda_fn_and_stub! {
    fn ab_sort_keys_d_u32(
        d_temp_storage: *mut u8,
        temp_storage_bytes: &mut usize,
        d_keys_in: *const u32,
        d_keys_out: *mut u32,
        num_items: u32,
        begin_bit: i32,
        end_bit: i32,
        stream: cudaStream_t,
    ) -> cudaError_t;
}

pub type SortKeysFunction<T> = unsafe extern "C" fn(
    *mut u8,
    &mut usize,
    *const T,
    *mut T,
    num_items: u32,
    begin_bit: i32,
    end_bit: i32,
    stream: cudaStream_t,
) -> cudaError_t;

pub trait SortKeys: Sized {
    fn get_function(descending: bool) -> SortKeysFunction<Self>;

    fn get_sort_keys_temp_storage_bytes(
        descending: bool,
        num_items: u32,
        begin_bit: i32,
        end_bit: i32,
    ) -> CudaResult<usize> {
        // CUB size-query mode is selected by passing null temp storage.
        // In that mode CUB only writes temp_storage_bytes and ignores data pointers.
        let mut temp_storage_bytes = 0;
        let function = Self::get_function(descending);
        unsafe {
            function(
                null_mut(),
                &mut temp_storage_bytes,
                null(),
                null_mut(),
                num_items,
                begin_bit,
                end_bit,
                null_mut(),
            )
            .wrap_value(temp_storage_bytes)
        }
    }

    fn sort_keys(
        descending: bool,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_keys_in: &DeviceSlice<Self>,
        d_keys_out: &mut DeviceSlice<Self>,
        begin_bit: i32,
        end_bit: i32,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let mut temp_storage_bytes = d_temp_storage.len();
        assert_eq!(d_keys_in.len(), d_keys_out.len());
        assert!(d_keys_out.len() <= u32::MAX as usize);
        let num_items = d_keys_out.len() as u32;
        let function = Self::get_function(descending);
        unsafe {
            function(
                d_temp_storage.as_mut_ptr(),
                &mut temp_storage_bytes,
                d_keys_in.as_ptr(),
                d_keys_out.as_mut_ptr(),
                num_items,
                begin_bit,
                end_bit,
                stream.into(),
            )
            .wrap()
        }
    }
}

impl SortKeys for u32 {
    fn get_function(descending: bool) -> SortKeysFunction<Self> {
        if descending {
            ab_sort_keys_d_u32
        } else {
            ab_sort_keys_a_u32
        }
    }
}

impl SortKeys for BF {
    fn get_function(descending: bool) -> SortKeysFunction<Self> {
        let function = if descending {
            ab_sort_keys_d_u32
        } else {
            ab_sort_keys_a_u32
        };
        // SAFETY: `BF` is a transparent `u32` newtype for this radix-sort path,
        // so the ABI matches the `u32` kernel entrypoints.
        unsafe { std::mem::transmute::<SortKeysFunction<u32>, SortKeysFunction<Self>>(function) }
    }

    fn sort_keys(
        descending: bool,
        d_temp_storage: &mut DeviceSlice<u8>,
        d_keys_in: &DeviceSlice<Self>,
        d_keys_out: &mut DeviceSlice<Self>,
        begin_bit: i32,
        end_bit: i32,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        let d_keys_in = unsafe { d_keys_in.transmute() };
        let d_keys_out = unsafe { d_keys_out.transmute_mut() };
        u32::sort_keys(
            descending,
            d_temp_storage,
            d_keys_in,
            d_keys_out,
            begin_bit,
            end_bit,
            stream,
        )
    }
}

pub fn get_sort_keys_temp_storage_bytes<T: SortKeys>(
    descending: bool,
    num_items: u32,
    begin_bit: i32,
    end_bit: i32,
) -> CudaResult<usize> {
    T::get_sort_keys_temp_storage_bytes(descending, num_items, begin_bit, end_bit)
}

pub fn sort_keys<T: SortKeys>(
    descending: bool,
    d_temp_storage: &mut DeviceSlice<u8>,
    d_keys_in: &DeviceSlice<T>,
    d_keys_out: &mut DeviceSlice<T>,
    begin_bit: i32,
    end_bit: i32,
    stream: &CudaStream,
) -> CudaResult<()> {
    T::sort_keys(
        descending,
        d_temp_storage,
        d_keys_in,
        d_keys_out,
        begin_bit,
        end_bit,
        stream,
    )
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use itertools::Itertools;
    use rand::distr::{Distribution, StandardUniform};
    use rand::random;
    use serial_test::serial;

    use super::*;

    fn test_sort_keys<T>(descending: bool)
    where
        T: SortKeys + Default + Clone + Ord + Eq,
        StandardUniform: Distribution<T>,
    {
        const NUM_ITEMS: usize = 1 << 16;
        let end_bit = size_of::<T>() as i32 * 8;
        let temp_storage_bytes =
            get_sort_keys_temp_storage_bytes::<T>(descending, NUM_ITEMS as u32, 0, end_bit)
                .unwrap();
        let mut d_temp_storage = DeviceAllocation::alloc(temp_storage_bytes).unwrap();
        let mut h_keys_in = (0..NUM_ITEMS).map(|_| random()).collect_vec();
        let mut h_keys_out = vec![T::default(); NUM_ITEMS];
        let mut d_keys_in = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
        let mut d_keys_out = DeviceAllocation::alloc(NUM_ITEMS).unwrap();
        let stream = CudaStream::default();
        memory_copy_async(&mut d_keys_in, &h_keys_in, &stream).unwrap();
        sort_keys(
            descending,
            &mut d_temp_storage,
            &d_keys_in,
            &mut d_keys_out,
            0,
            end_bit,
            &stream,
        )
        .unwrap();
        memory_copy_async(&mut h_keys_out, &d_keys_out, &stream).unwrap();
        stream.synchronize().unwrap();
        h_keys_in.sort();
        if descending {
            h_keys_in.reverse()
        };
        assert!(h_keys_in
            .into_iter()
            .zip(h_keys_out.into_iter())
            .all(|(x, y)| x == y));
    }

    #[test]
    #[serial]
    fn sort_keys_a_u32() {
        test_sort_keys::<u32>(false);
    }

    #[test]
    #[serial]
    fn sort_keys_d_u32() {
        test_sort_keys::<u32>(true);
    }
}
