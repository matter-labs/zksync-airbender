use crate::GoodAllocator;
// Only the `#[cfg(test)]` module below needs field types (via `use super::*`).
#[cfg(test)]
use ::field::*;

pub(crate) const TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE: usize = 3;
pub(crate) const TINY_BITREVERSE_LOOKUP_TABLE: [u8; 1 << TINY_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE] = const {
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
pub(crate) const MEDIUM_BITREVERSE_LOOKUP_TABLE: [u8; 1
    << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE] = const {
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
    if input.is_empty() {
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
pub fn parallel_bitreverse_enumeration_inplace<T: Copy + Send>(input: &mut [T], worker: &Worker) {
    if input.is_empty() {
        return;
    }
    assert!(input.len().is_power_of_two());

    if input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_small_lookup(input);
    } else if input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_medium_lookup(input);
    } else if input.len() >= BLOCKED_BITREVERSE_MIN_LEN && blocked_bitreverse_applies::<T>() {
        parallel_blocked_bitreverse_enumeration_inplace(input, worker);
    } else if input.len() <= 1usize << 27 {
        parallel_optimized_bitreverse_enumeration_inplace(input, worker);
    } else {
        parallel_simple_bitreverse_enumeration_inplace(input, worker);
    }
}

// ---------------------------------------------------------------------------
// Cache-blocked (COBRA-style) in-place bit reversal
// ---------------------------------------------------------------------------
//
// Index `i = (a << (L - q)) | (b << q) | c` (`a`: top `q` bits, `b`: the
// middle `L - 2q` bits, `c`: low `q` bits) is sent to
// `rev(i) = (rev_q(c) << (L - q)) | (rev(b) << q) | rev_q(a)`: the tile of
// middle bits `b` (a `2^q x 2^q` grid of `(a, c)`) lands, transposed and with
// both coordinates bit-reversed, on the tile `rev(b)`. A tile is read as `2^q`
// contiguous runs of `2^q` elements (fixed `a`, `c` running) into an
// L1-resident buffer laid out as `buf[(c << q) | rev_q(a)]`, and the
// destination tile is written as `2^q` contiguous runs
// (`out[a', rev(b), c']` for `c'` running is `buf` row `rev_q(a')`). So every
// access to the big array is a contiguous run and the random part of the
// permutation happens in the buffer. Tiles `b` and `rev(b)` are swapped
// pairwise in place; fixed points (`b == rev(b)`) go through one buffer.

/// Tile width log2 for the blocked bit reversal: a tile of `2^(2q)` elements
/// stays well inside L1 for both 4-byte and 16-byte elements.
const fn blocked_bitreverse_q<T>(log_n: u32) -> u32 {
    let q = if core::mem::size_of::<T>() <= 4 { 7 } else { 6 };
    if log_n >= 2 * q {
        q
    } else {
        log_n / 2
    }
}

#[inline(always)]
fn rev_bits(x: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        x.reverse_bits() >> (usize::BITS - bits)
    }
}

/// Load tile `b` into `buf[(c << q) | rev_q(a)] = v[a, b, c]`.
#[inline(always)]
unsafe fn cobra_load_tile<T: Copy>(v: *const T, log_n: u32, q: u32, b: usize, buf: &mut [T]) {
    let run = 1usize << q;
    let a_shift = log_n - q;
    for a in 0..run {
        let ra = rev_bits(a, q);
        let src = v.add((a << a_shift) | (b << q));
        for c in 0..run {
            *buf.get_unchecked_mut((c << q) | ra) = *src.add(c);
        }
    }
}

/// Write tile `dst_b` from the buffer of tile `src_b` (`dst_b == rev(src_b)`):
/// `v[a', dst_b, c'] = buf[(rev_q(a') << q) | c']` — contiguous rows.
#[inline(always)]
unsafe fn cobra_store_tile<T: Copy>(v: *mut T, log_n: u32, q: u32, dst_b: usize, buf: &[T]) {
    let run = 1usize << q;
    let a_shift = log_n - q;
    for a in 0..run {
        let ra = rev_bits(a, q);
        let dst = v.add((a << a_shift) | (dst_b << q));
        core::ptr::copy_nonoverlapping(buf.as_ptr().add(ra << q), dst, run);
    }
}

/// The tile pairs `(b, rev(b))` with `b <= rev(b)` of the middle `mid_bits`.
fn cobra_tile_pairs(mid_bits: u32) -> Vec<(usize, usize)> {
    (0..1usize << mid_bits)
        .filter_map(|b| {
            let rb = rev_bits(b, mid_bits);
            (b <= rb).then_some((b, rb))
        })
        .collect()
}

/// Permute the tile pairs `pairs` of `input` (which must be `2^log_n` long)
/// with tile width `q`.
unsafe fn cobra_permute_pairs<T: Copy>(
    v: *mut T,
    log_n: u32,
    q: u32,
    pairs: &[(usize, usize)],
    buf_a: &mut [T],
    buf_b: &mut [T],
) {
    for &(b, rb) in pairs {
        if b == rb {
            cobra_load_tile(v, log_n, q, b, buf_a);
            cobra_store_tile(v, log_n, q, b, buf_a);
        } else {
            cobra_load_tile(v, log_n, q, b, buf_a);
            cobra_load_tile(v, log_n, q, rb, buf_b);
            cobra_store_tile(v, log_n, q, rb, buf_a);
            cobra_store_tile(v, log_n, q, b, buf_b);
        }
    }
}

/// Below this length the lookup / small-run permutations stay.
const BLOCKED_BITREVERSE_MIN_LEN: usize = 1 << 12;

/// The blocked permutation pays off for 4-byte elements only (M3, 2^23 u32:
/// 11.2 -> 7.0 ms with `q = 7`); for 16-byte elements its scalar tile
/// transpose loses to the 8-element-run permutation (2^22 Ext4: 6.1 vs
/// 10.8 ms), which therefore stays.
const fn blocked_bitreverse_applies<T>() -> bool {
    core::mem::size_of::<T>() <= 4
}

/// [`bitreverse_enumeration_inplace`] for `Copy` elements, cache-blocked for
/// large arrays (above [`BLOCKED_BITREVERSE_MIN_LEN`]): both the reads and the
/// writes of the array are contiguous runs of `2^q` elements, the random
/// access happens in an L1-resident tile buffer. Same permutation.
pub fn bitreverse_enumeration_inplace_blocked<T: Copy>(input: &mut [T]) {
    if input.len() < BLOCKED_BITREVERSE_MIN_LEN || !blocked_bitreverse_applies::<T>() {
        return bitreverse_enumeration_inplace(input);
    }
    let log_n = input.len().trailing_zeros();
    bitreverse_enumeration_inplace_blocked_q(input, blocked_bitreverse_q::<T>(log_n));
}

/// [`bitreverse_enumeration_inplace_blocked`] with an explicit tile width
/// (`2q <= log2 len`); for tuning.
pub fn bitreverse_enumeration_inplace_blocked_q<T: Copy>(input: &mut [T], q: u32) {
    assert!(input.len().is_power_of_two());
    let log_n = input.len().trailing_zeros();
    assert!(2 * q <= log_n);
    let tile = 1usize << (2 * q);
    let mut buf_a = vec![input[0]; tile];
    let mut buf_b = vec![input[0]; tile];
    let pairs = cobra_tile_pairs(log_n - 2 * q);
    unsafe {
        cobra_permute_pairs(input.as_mut_ptr(), log_n, q, &pairs, &mut buf_a, &mut buf_b);
    }
}

fn parallel_blocked_bitreverse_enumeration_inplace<T: Copy + Send>(
    input: &mut [T],
    worker: &Worker,
) {
    assert!(input.len().is_power_of_two());
    let log_n = input.len().trailing_zeros();
    let q = blocked_bitreverse_q::<T>(log_n);
    let tile = 1usize << (2 * q);
    let pairs = cobra_tile_pairs(log_n - 2 * q);
    let first = input[0];
    let ptr = input.as_mut_ptr() as usize;
    let pairs_ref = &pairs[..];
    worker.scope(pairs.len(), |scope, geometry| {
        for chunk_idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(chunk_idx);
            let size = geometry.get_chunk_size(chunk_idx);
            Worker::smart_spawn(scope, chunk_idx == geometry.len() - 1, move |_| {
                let mut buf_a = vec![first; tile];
                let mut buf_b = vec![first; tile];
                unsafe {
                    cobra_permute_pairs(
                        ptr as *mut T,
                        log_n,
                        q,
                        &pairs_ref[start..start + size],
                        &mut buf_a,
                        &mut buf_b,
                    );
                }
            });
        }
    });
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
/// of type U. Capacity should be divisible by `size_of::<U>() / size_of::<T>()`.
#[inline]
pub fn allocate_in_with_alignment_of<T: Sized, U: Sized, A: GoodAllocator>(
    capacity: usize,
    allocator: A,
) -> Vec<T, A> {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>().is_multiple_of(std::mem::size_of::<T>()));
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    if size_factor == 0 {
        return Vec::with_capacity_in(capacity, allocator);
    }
    debug_assert!(capacity.is_multiple_of(size_factor));
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
#[allow(clippy::ptr_arg)]
pub fn clone_respecting_alignment<T: Sized + Clone, U: Sized, A: GoodAllocator>(
    input: &Vec<T, A>,
) -> Vec<T, A> {
    // we can not just use alignment of pointer in the input because it can be larger
    let mut result = allocate_in_with_alignment_of::<T, U, _>(input.len(), A::default());
    result.extend_from_slice(input);

    result
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment<T: Sized, U: Sized, A: GoodAllocator>(a: Vec<T, A>) -> Vec<U, A> {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>().is_multiple_of(std::mem::size_of::<T>()));
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
    debug_assert!(std::mem::size_of::<U>().is_multiple_of(std::mem::size_of::<T>()));
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    debug_assert!(size_factor > 0);
    let len = a.len();
    let ptr = a.as_mut_ptr();
    debug_assert!(len.is_multiple_of(size_factor));
    debug_assert!(ptr.addr().is_multiple_of(std::mem::align_of::<U>()));
    let modified_len = len / size_factor;
    unsafe { std::slice::from_raw_parts_mut(ptr as *mut U, modified_len) }
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment_ref_mut_unpack<T: Sized, U: Sized>(a: &mut [T]) -> &mut [U] {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<T>().is_multiple_of(std::mem::size_of::<U>()));
    let size_factor = std::mem::size_of::<T>() / std::mem::size_of::<U>();
    debug_assert!(size_factor > 0);
    let len = a.len();
    let ptr = a.as_mut_ptr();
    debug_assert!(ptr.addr().is_multiple_of(std::mem::align_of::<U>()));
    let modified_len = len * size_factor;
    unsafe { std::slice::from_raw_parts_mut(ptr as *mut U, modified_len) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocked_bitreverse_matches_simple() {
        for log_n in [12u32, 13, 14, 15, 17, 21] {
            let n = 1usize << log_n;
            let mut st = 0x1234_5678_9abc_def0u64 ^ log_n as u64;
            let mut next = || {
                st = st
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                (st >> 7) as u32
            };
            let words: Vec<u32> = (0..n).map(|_| next()).collect();
            let quads: Vec<[u32; 4]> = (0..n).map(|_| [next(), next(), next(), next()]).collect();
            let mut expected_w = words.clone();
            simple_bitreverse_enumeration_inplace(&mut expected_w);
            let mut got_w = words.clone();
            bitreverse_enumeration_inplace_blocked(&mut got_w);
            assert_eq!(got_w, expected_w, "u32 log_n {log_n}");
            let mut expected_q = quads.clone();
            simple_bitreverse_enumeration_inplace(&mut expected_q);
            let mut got_q = quads.clone();
            bitreverse_enumeration_inplace_blocked(&mut got_q);
            assert_eq!(got_q, expected_q, "quad log_n {log_n}");
            for threads in [1usize, 3, 8] {
                let worker = Worker::new_with_num_threads(threads);
                let mut par_w = words.clone();
                parallel_bitreverse_enumeration_inplace(&mut par_w, &worker);
                assert_eq!(
                    par_w, expected_w,
                    "parallel u32 log_n {log_n} thr {threads}"
                );
                let mut par_q = quads.clone();
                parallel_bitreverse_enumeration_inplace(&mut par_q, &worker);
                assert_eq!(
                    par_q, expected_q,
                    "parallel quad log_n {log_n} thr {threads}"
                );
            }
        }
    }

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
            .map(|_| Mersenne31Field::from_u32_with_reduction(rng.random_range(0..(1 << 31) - 1)))
            .collect()
    }
}
