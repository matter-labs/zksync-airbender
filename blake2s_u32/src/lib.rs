#![cfg_attr(not(test), no_std)]
#![feature(ptr_as_ref_unchecked)]

// special purpose designated blake2s implementaition, that has no internal buffer,
// and operates on u32 basis. Has options for reduced number of rounds

mod asm_utils;
pub(crate) mod baseline;
mod mixing_function;
pub mod vectorized_impls;

pub use mixing_function::{
    mixing_function, round_function_full_rounds, round_function_reduced_rounds,
};

#[cfg(test)]
mod test;

pub const BLAKE2S_ROUNDS: usize = 10;
pub const BLAKE2S_REDUCED_ROUNDS: usize = 7;

pub const BLAKE2S_BLOCK_SIZE_U32_WORDS: usize = 16;
pub const BLAKE2S_BLOCK_SIZE_BYTES: usize = 64;
pub const BLAKE2S_DIGEST_SIZE_U32_WORDS: usize = 8;
pub const BLAKE2S_STATE_WIDTH_IN_U32_WORDS: usize = 8;
pub const BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS: usize = 16;

pub const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

// default configured to no tree, and 32 bytes digest output
pub const IV_0_TWIST: u32 = 0x6A09E667 ^ 0x01010000 ^ 32;

pub const SIGMAS: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

pub const CONFIGURED_IV: [u32; 8] = const {
    let mut result = IV;
    result[0] = IV_0_TWIST;

    result
};

pub const EXTENDED_CONFIGURED_IV: [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] = const {
    let mut result = [0u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS];
    let mut i = 0;
    while i < 8 {
        result[i] = CONFIGURED_IV[i];
        result[8 + i] = IV[i];
        i += 1;
    }

    result
};

pub use self::baseline::Blake2sState;

#[cfg(not(feature = "blake2_with_compression"))]
pub use self::baseline::Blake2sState as DelegatedBlake2sState;

pub mod state_with_extended_control;

#[cfg(feature = "blake2_with_compression")]
pub use self::state_with_extended_control::Blake2RoundFunctionEvaluator as DelegatedBlake2sState;

pub mod state_with_extended_control_flags {
    use crate::BLAKE2S_BLOCK_SIZE_BYTES;
    use crate::EXTENDED_CONFIGURED_IV;

    pub const LAST_ROUND_BIT_IDX: usize = 0;
    pub const INPUT_IS_RIGHT_NODE_BIT_IDX: usize = 1;
    pub const COMPRESSION_MODE_BIT_IDX: usize = 2;

    pub const TEST_IF_LAST_ROUND_MASK: u32 = 1 << LAST_ROUND_BIT_IDX;
    pub const TEST_IF_INPUT_IS_RIGHT_NODE_MASK: u32 = 1 << INPUT_IS_RIGHT_NODE_BIT_IDX;
    pub const TEST_IF_COMPRESSION_MODE_MASK: u32 = 1 << COMPRESSION_MODE_BIT_IDX;

    pub const COMPRESSION_MODE_EXTENDED_CONFIGURED_IV: [u32; 16] = const {
        let mut result = EXTENDED_CONFIGURED_IV;
        result[12] ^= BLAKE2S_BLOCK_SIZE_BYTES as u32;
        result[14] ^= 0xffffffff;

        result
    };
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn spec_memzero_u32(mut dst: *mut u32, end: *mut u32) {
    core::hint::assert_unchecked(dst.addr() % 4 == 0);
    core::hint::assert_unchecked(end.addr() % 4 == 0);
    while dst < end {
        // this prevents LLVM to insert memset, but fine for our purposes
        dst.write_volatile(0);
        dst = dst.add(1);
    }
}

#[cfg(not(target_arch = "riscv32"))]
#[inline(always)]
pub unsafe fn spec_memzero_u32(mut dst: *mut u32, end: *mut u32) {
    debug_assert!(dst.addr() % 4 == 0);
    debug_assert!(end.addr() % 4 == 0);
    core::hint::assert_unchecked(dst.addr() % 4 == 0);
    core::hint::assert_unchecked(end.addr() % 4 == 0);
    while dst < end {
        dst.write(0);
        dst = dst.add(1);
    }
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn spec_memcopy_u32_nonoverlapping(
    mut src: *const u32,
    mut dst: *mut u32,
    count: usize,
) {
    core::hint::assert_unchecked(src.addr() % 4 == 0);
    core::hint::assert_unchecked(dst.addr() % 4 == 0);
    let end = dst.add(count);
    while dst < end {
        // this prevents LLVM to insert memcpy, but fine for our purposes
        dst.write_volatile(src.read());
        dst = dst.add(1);
        src = src.add(1);
    }
}

#[cfg(not(target_arch = "riscv32"))]
#[inline(always)]
pub unsafe fn spec_memcopy_u32_nonoverlapping(src: *const u32, dst: *mut u32, count: usize) {
    core::ptr::copy_nonoverlapping(src, dst, count);
}

#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub unsafe fn spec_memcmp_u32_nonoverlapping(
    mut src: *const u32,
    mut dst: *const u32,
    count: usize,
) -> bool {
    let mut equal = true;
    let end = dst.add(count);
    while dst < end && equal {
        equal &= dst.read_volatile() == src.read_volatile();
        dst = dst.add(1);
        src = src.add(1);
    }

    equal
}

#[cfg(target_arch = "riscv32")]
#[inline]
pub unsafe fn spec_memcopy<T: Sized + Copy>(src: &T, dst: &mut T) {
    debug_assert!(core::mem::align_of::<T>() >= 4);
    debug_assert!(core::mem::size_of::<T>() >= 4);
    core::hint::assert_unchecked(core::mem::align_of::<T>() >= 4);
    core::hint::assert_unchecked(core::mem::size_of::<T>() >= 4);
    spec_memcopy_u32_nonoverlapping(
        (src as *const T).cast::<u32>(),
        (dst as *mut T).cast::<u32>(),
        core::mem::size_of::<T>() / core::mem::size_of::<u32>(),
    );
}

#[cfg(not(target_arch = "riscv32"))]
#[inline(always)]
pub unsafe fn spec_memcopy<T: Sized + Copy>(src: &T, dst: &mut T) {
    debug_assert!(core::mem::align_of::<T>() >= 4);
    debug_assert!(core::mem::size_of::<T>() >= 4);
    *dst = *src;
}

#[cfg(target_arch = "riscv32")]
#[inline]
pub unsafe fn spec_memcmp<T: Sized + Copy + Eq>(src: &T, dst: &T) -> bool {
    if core::mem::size_of::<T>() == 0 {
        true
    } else {
        debug_assert!(core::mem::align_of::<T>() >= 4);
        debug_assert!(core::mem::size_of::<T>() >= 4);
        core::hint::assert_unchecked(core::mem::align_of::<T>() >= 4);
        core::hint::assert_unchecked(core::mem::size_of::<T>() >= 4);
        spec_memcmp_u32_nonoverlapping(
            (src as *const T).cast::<u32>(),
            (dst as *const T).cast::<u32>(),
            core::mem::size_of::<T>() / core::mem::size_of::<u32>(),
        )
    }
}

#[cfg(not(target_arch = "riscv32"))]
#[inline(always)]
pub unsafe fn spec_memcmp<T: Sized + Copy + Eq>(src: &T, dst: &T) -> bool {
    *src == *dst
}
