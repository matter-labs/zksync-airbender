use crate::GoodAllocator;
use ::field::*;

// for: https://www.robinscheibler.org/2013/02/13/real-fft.html
pub fn pack_reals_as_complex<F: Field, E: FieldExtension<F>>(
    left: &[F],
    right: &[F],
    res_buf: &mut [E],
) {
    assert_eq!(left.len(), right.len());
    assert_eq!(left.len(), res_buf.len());
    assert_eq!(E::DEGREE, 2);

    left.iter()
        .zip(right.iter())
        .zip(res_buf.iter_mut())
        .for_each(|((left, right), out)| *out = E::from_coeffs_in_base(&[*left, *right]))
}

pub fn unpack_complex_into_reals<F: Field, E: FieldExtension<F>>(
    input: &[E],
    left_res: &mut [F],
    right_res: &mut [F],
) {
    assert_eq!(left_res.len(), right_res.len());
    assert_eq!(left_res.len(), input.len());
    assert_eq!(E::DEGREE, 2);

    left_res
        .iter_mut()
        .zip(right_res.iter_mut())
        .zip(input.iter())
        .for_each(|((left, right), input)| {
            let elems_in_base = input.coeffs_in_base();
            *left = elems_in_base[0];
            *right = elems_in_base[1];
        })
}

const TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE: usize = 3;
const TINY_BITREVERSE_LOOKUP_TABLE: [u8; 1 << TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE] = const {
    let mut result = [0u8; 1 << TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE];
    let mut i = 0u64;
    let shift_right = 64 - TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE;
    while i < (1 << TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE) {
        let reversed = i.reverse_bits() >> shift_right;
        debug_assert!(reversed <= u8::MAX as u64);
        result[i as usize] = reversed as u8;
        i += 1;
    }

    result
};

// swap via lookup table that itself fits into cache line
const SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE: usize = 6;
const SMALL_BITREVERSE_LOOKUP_TABLE: [u8; 1 << SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE] = const {
    let mut result = [0u8; 1 << SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE];
    let mut i = 0u64;
    let shift_right = 64 - SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE;
    while i < (1 << SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE) {
        let reversed = i.reverse_bits() >> shift_right;
        debug_assert!(reversed <= u8::MAX as u64);
        result[i as usize] = reversed as u8;
        i += 1;
    }

    result
};

// in this case we can easily swap bytes, and then swap bits in bytes
const MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE: usize = 8;
const MEDIUM_BITREVERSE_LOOKUP_TABLE: [u8; 1 << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE] = const {
    let mut result = [0u8; 1 << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE];
    let mut i = 0u64;
    let shift_right = 64 - MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE;
    while i < (1 << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE) {
        let reversed = i.reverse_bits() >> shift_right;
        debug_assert!(reversed <= u8::MAX as u64);
        result[i as usize] = reversed as u8;
        i += 1;
    }

    result
};

// This operation is so cache-unfriendly, that parallelism is not used here
pub const fn bitreverse_enumeration_inplace<T>(input: &mut [T]) {
    if input.len() == 0 {
        return;
    }
    assert!(input.len().is_power_of_two());

    if input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_small_lookup(input);
    } else if input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_medium_lookup(input);
    } else if input.len() <= 1usize << 27 {
        optimized_bitreverse_enumeration_inplace(input);
    } else {
        simple_bitreverse_enumeration_inplace(input);
    }
}

const fn bitreverse_enumeration_inplace_via_small_lookup<T>(input: &mut [T]) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len());

    let shift_to_cleanup =
        (SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32) - input.len().trailing_zeros();

    let mut i = 0;
    let work_size = input.len();
    while i < work_size {
        let mut j = SMALL_BITREVERSE_LOOKUP_TABLE[i] as usize;
        j >>= shift_to_cleanup; // if our table size is larger than work size
        if i < j {
            unsafe { input.swap_unchecked(i, j) };
        }

        i += 1;
    }
}

const fn bitreverse_enumeration_inplace_via_medium_lookup<T>(input: &mut [T]) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len());

    let shift_to_cleanup =
        (MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32) - input.len().trailing_zeros();

    let mut i = 0;
    let work_size = input.len();
    while i < work_size {
        let mut j = MEDIUM_BITREVERSE_LOOKUP_TABLE[i] as usize;
        j >>= shift_to_cleanup; // if our table size is larger than work size
        if i < j {
            unsafe { input.swap_unchecked(i, j) };
        }

        i += 1;
    }
}

const fn optimized_bitreverse_enumeration_inplace<T>(input: &mut [T]) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() > MEDIUM_BITREVERSE_LOOKUP_TABLE.len());
    assert!(input.len() <= 1usize << 27); // 3 bytes + 3 high bits

    // there is a function usize::reverse_bits(), but if one looks into the compiler then
    // will see that it's something like (sorry for C code)
    // ```
    //     uint32_t bit_reverse32(uint32_t x)
    // {
    //     x = (x >> 16) | (x << 16);
    //     x = ((x & 0xFF00FF00) >> 8) | ((x & 0x00FF00FF) << 8);
    //     x = ((x & 0xF0F0F0F0) >> 4) | ((x & 0x0F0F0F0F) << 4);
    //     x = ((x & 0xCCCCCCCC) >> 2) | ((x & 0x33333333) << 2);
    //     return ((x & 0xAAAAAAAA) >> 1) | ((x & 0x55555555) << 1);
    // }
    // ```

    // since we bitreverse a continuous set of indexes, we can save a little by
    // doing two loops, such that one bitreverses (naively) some common bits,
    // and one that bitreversed uncommon via lookup

    let log_n = input.len().trailing_zeros();
    let common_part_log_n = log_n - (TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32);

    // double loop. Note the swapping approach:
    // - lowest bits become highest bits and change every time
    // - highest bits change become lowest bits and change rarely
    // so our "i" counter is a counter over lowest bits, and our source is in the form i + (j << common_part_log_n)
    // and our dst is reversed_j + reversed_i << 3
    // and since our source and destination are symmetrical we can formally swap them
    // and have our writes cache-friendly
    let mut i = 0;
    let work_size = 1u32 << common_part_log_n;
    while i < work_size {
        // bitreversing byte by byte
        let mut bytes = i.swap_bytes().to_le_bytes();
        bytes[0] = 0;
        bytes[1] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[1] as usize];
        bytes[2] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[2] as usize];
        bytes[3] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[3] as usize];
        let reversed_i = u32::from_le_bytes(bytes) >> (32 - common_part_log_n);

        debug_assert!(reversed_i == i.reverse_bits() >> (32 - common_part_log_n));

        let mut j = 0;
        while j < TINY_BITREVERSE_LOOKUP_TABLE.len() {
            let reversed_j = TINY_BITREVERSE_LOOKUP_TABLE[j];
            let dst = (i as usize) | (j << common_part_log_n);
            let src = (reversed_j as usize)
                | ((reversed_i as usize) << TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE);
            if dst < src {
                unsafe { input.swap_unchecked(src, dst) };
            }

            j += 1;
        }

        i += 1;
    }
}

const fn simple_bitreverse_enumeration_inplace<T>(input: &mut [T]) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() > MEDIUM_BITREVERSE_LOOKUP_TABLE.len());
    assert!(input.len() <= 1usize << 31); // a reasonable upper bound to use u32 internally

    let log_n = input.len().trailing_zeros();

    let mut i = 0;
    while i < input.len() {
        let mut bytes = (i as u32).swap_bytes().to_le_bytes();
        bytes[0] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[0] as usize];
        bytes[1] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[1] as usize];
        bytes[2] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[2] as usize];
        bytes[3] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[3] as usize];

        let reversed_i = (u32::from_le_bytes(bytes) >> (32 - log_n)) as usize;

        if reversed_i < i {
            unsafe { input.swap_unchecked(i, reversed_i) };
        }

        i += 1;
    }
}

use worker::Worker;
pub fn parallel_bitreverse_enumeration_inplace<T>(input: &mut [T], worker: &Worker) {
    if input.len() == 0 {
        return;
    }
    assert!(input.len().is_power_of_two());

    if input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_small_lookup(input);
    } else if input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_medium_lookup(input);
    } else if input.len() <= 1usize << 27 {
        parallel_optimized_bitreverse_enumeration_inplace(input, worker);
    } else {
        parallel_simple_bitreverse_enumeration_inplace(input, worker);
    }
}

fn parallel_optimized_bitreverse_enumeration_inplace<T>(input: &mut [T], worker: &Worker) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() > TINY_BITREVERSE_LOOKUP_TABLE.len());
    assert!(input.len() <= 1usize << 27); // 3 bytes + 3 high bits

    let log_n = input.len().trailing_zeros();
    let size = input.len();

    let common_part_log_n = log_n - (TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32);

    let work_size = 1u32 << common_part_log_n;

    let ptr = input.as_ptr() as u64;
    worker.scope(work_size as usize, |scope, geometry| {
        for chunk_idx in 0..geometry.num_chunks {
            scope.spawn(move |_| {
                let input_clone = unsafe { core::slice::from_raw_parts_mut(ptr as *mut T, size) };

                let chunk_start = geometry.get_chunk_start_pos(chunk_idx);
                let chunk_range = chunk_start..chunk_start + geometry.get_chunk_size(chunk_idx);

                for i in chunk_range {
                    // bitreversing byte by byte
                    let mut bytes = (i as u32).swap_bytes().to_le_bytes();
                    bytes[0] = 0;
                    bytes[1] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[1] as usize];
                    bytes[2] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[2] as usize];
                    bytes[3] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[3] as usize];
                    let reversed_i = u32::from_le_bytes(bytes) >> (32 - common_part_log_n);

                    // debug_assert!(reversed_i == i.reverse_bits() >> (32 - common_part_log_n));

                    let mut j = 0;
                    while j < TINY_BITREVERSE_LOOKUP_TABLE.len() {
                        let reversed_j = TINY_BITREVERSE_LOOKUP_TABLE[j];
                        let dst = i | (j << common_part_log_n);
                        let src = (reversed_j as usize)
                            | ((reversed_i as usize) << TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE);
                        if dst < src {
                            unsafe { input_clone.swap_unchecked(src, dst) };
                        }

                        j += 1;
                    }
                }
            });
        }
    });
}

fn parallel_simple_bitreverse_enumeration_inplace<T>(input: &mut [T], worker: &Worker) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() > MEDIUM_BITREVERSE_LOOKUP_TABLE.len());
    assert!(input.len() <= 1usize << 31); // a reasonable upper bound to use u32 internally

    let log_n = input.len().trailing_zeros();
    let size = input.len();

    let ptr = input.as_ptr() as usize;
    worker.scope(size, |scope, geometry| {
        for chunk_idx in 0..geometry.num_chunks {
            scope.spawn(move |_| {
                let input_clone = unsafe { core::slice::from_raw_parts_mut(ptr as *mut T, size) };

                let chunk_start = geometry.get_chunk_start_pos(chunk_idx);
                let chunk_range = chunk_start..chunk_start + geometry.get_chunk_size(chunk_idx);

                for i in chunk_range {
                    let mut bytes = (i as u32).swap_bytes().to_le_bytes();
                    bytes[0] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[0] as usize];
                    bytes[1] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[1] as usize];
                    bytes[2] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[2] as usize];
                    bytes[3] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[3] as usize];

                    let reversed_i = (u32::from_le_bytes(bytes) >> (32 - log_n)) as usize;

                    if reversed_i < i {
                        unsafe { input_clone.swap_unchecked(i, reversed_i) };
                    }
                }
            });
        }
    });
}

pub const fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    let t = index << (usize::BITS - num_bits);
    t.reverse_bits()
}

/// Allocate a vector of type T, but with extra restriction that it has an alignment
/// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn allocate_in_with_alignment_of<T: Sized, U: Sized, A: GoodAllocator>(
    capacity: usize,
    allocator: A,
) -> Vec<T, A> {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>() % std::mem::size_of::<T>() == 0);
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    if size_factor == 0 {
        return Vec::with_capacity_in(capacity, allocator);
    }
    debug_assert!(capacity % size_factor == 0);
    let modified_capacity = capacity / size_factor;
    let (ptr, len, _, allocator) =
        Vec::<U, A>::with_capacity_in(modified_capacity, allocator).into_raw_parts_with_alloc();
    debug_assert_eq!(len, 0);
    unsafe { Vec::<T, A>::from_raw_parts_in(ptr as *mut T, len, capacity, allocator) }
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn allocate_with_alignment_of<T: Sized, U: Sized>(capacity: usize) -> Vec<T> {
    allocate_in_with_alignment_of::<T, U, std::alloc::Global>(capacity, std::alloc::Global)
}

#[inline]
pub fn initialize_in_with_alignment_of<T: Sized + Copy, U: Sized, A: GoodAllocator>(
    value: T,
    length: usize,
    allocator: A,
) -> Vec<T, A> {
    let mut new = allocate_in_with_alignment_of::<T, U, A>(length, allocator);
    new.resize(length, value);

    new
}

#[inline]
pub fn initialize_with_alignment_of<T: Sized + Copy, U: Sized>(value: T, length: usize) -> Vec<T> {
    let mut new = allocate_with_alignment_of::<T, U>(length);
    new.resize(length, value);

    new
}

#[inline]
pub fn clone_respecting_alignment<T: Sized + Clone, U: Sized, A: GoodAllocator>(
    input: &Vec<T, A>,
) -> Vec<T, A> {
    // we can not just use alignment of pointer in the input because it can be larger
    let mut result = allocate_in_with_alignment_of::<T, U, _>(input.len(), A::default());
    result.extend_from_slice(&input[..]);

    result
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment<T: Sized, U: Sized, A: GoodAllocator>(a: Vec<T, A>) -> Vec<U, A> {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>() % std::mem::size_of::<T>() == 0);
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    debug_assert!(size_factor > 0);
    let (ptr, len, capacity, allocator) = a.into_raw_parts_with_alloc();
    debug_assert!(len % size_factor == 0);
    debug_assert!(capacity % size_factor == 0);
    debug_assert!(ptr.addr() % std::mem::align_of::<U>() == 0);
    let modified_len = len / size_factor;
    let modified_capacity = capacity / size_factor;
    unsafe {
        Vec::<U, A>::from_raw_parts_in(ptr as *mut U, modified_len, modified_capacity, allocator)
    }
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment_ref_mut_pack<T: Sized, U: Sized>(a: &mut [T]) -> &mut [U] {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>() % std::mem::size_of::<T>() == 0);
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    debug_assert!(size_factor > 0);
    let len = a.len();
    let ptr = a.as_mut_ptr();
    debug_assert!(len % size_factor == 0);
    debug_assert!(ptr.addr() % std::mem::align_of::<U>() == 0);
    let modified_len = len / size_factor;
    unsafe { std::slice::from_raw_parts_mut(ptr as *mut U, modified_len) }
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment_ref_mut_unpack<T: Sized, U: Sized>(a: &mut [T]) -> &mut [U] {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<T>() % std::mem::size_of::<U>() == 0);
    let size_factor = std::mem::size_of::<T>() / std::mem::size_of::<U>();
    debug_assert!(size_factor > 0);
    let len = a.len();
    let ptr = a.as_mut_ptr();
    debug_assert!(ptr.addr() % std::mem::align_of::<U>() == 0);
    let modified_len = len * size_factor;
    unsafe { std::slice::from_raw_parts_mut(ptr as *mut U, modified_len) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitreverse() {
        const SIZE_LOG: usize = 20;
        const SIZE: usize = 1 << SIZE_LOG;

        let original_data = get_random_slice(SIZE);
        let worker_2 = Worker::new_with_num_threads(2);
        let worker_4 = Worker::new_with_num_threads(4);

        // Cache optimized
        let mut expected_result = original_data.clone();
        simple_bitreverse_enumeration_inplace(&mut expected_result);

        // Simple
        let mut data = original_data.clone();
        bitreverse_enumeration_inplace(&mut data);
        assert_eq!(data, expected_result);

        // Parallel 2
        let mut data = original_data.clone();
        parallel_bitreverse_enumeration_inplace(&mut data, &worker_2);
        assert_eq!(data, expected_result);

        // Parallel 4
        let mut data = original_data.clone();
        parallel_bitreverse_enumeration_inplace(&mut data, &worker_4);
        assert_eq!(data, expected_result);
    }

    fn get_random_slice(len: usize) -> Vec<Mersenne31Field> {
        use rand::Rng;
        let mut rng = rand::rng();

        (0..len)
            .map(|_| Mersenne31Field::from_u64(rng.random_range(0..(1 << 31) - 1)).unwrap())
            .collect()
    }
}
