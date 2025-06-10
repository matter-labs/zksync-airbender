#![feature(allocator_api)]
#![feature(slice_swap_unchecked)]
#![cfg_attr(target_arch = "aarch64", feature(stdarch_aarch64_prefetch))]

use field::Mersenne31ComplexVectorizedInterleaved;
use field::Mersenne31Field;

pub mod column_major;
pub mod field_utils;
pub mod grinded_fft;
pub mod row_major;
pub mod utils;

pub use self::column_major::*;
pub use self::field_utils::*;
pub use self::grinded_fft::*;
pub use self::row_major::*;
pub use self::utils::*;

pub trait GoodAllocator:
    std::alloc::Allocator + Clone + Default + Send + Sync + std::fmt::Debug
{
}
impl GoodAllocator for std::alloc::Global {}

#[cfg(target_arch = "aarch64")]
pub const CACHE_LINE_WIDTH: usize = 128;

#[cfg(not(target_arch = "aarch64"))]
pub const CACHE_LINE_WIDTH: usize = 64;

pub const L1_CACHE_SIZE: usize = 1 << 17;

pub const CACHE_LINE_MULTIPLE: usize = const {
    assert!(core::mem::size_of::<Mersenne31Field>() >= core::mem::align_of::<Mersenne31Field>());

    CACHE_LINE_WIDTH / core::mem::size_of::<Mersenne31Field>()
};

pub const VECTORIZED_MULTIPLE: usize = const {
    assert!(core::mem::size_of::<Mersenne31Field>() >= core::mem::align_of::<Mersenne31Field>());

    core::mem::size_of::<Mersenne31ComplexVectorizedInterleaved>()
        / core::mem::size_of::<Mersenne31Field>()
};

#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn prefetch_next_line(ptr: *const Mersenne31Field) {
    use core::arch::aarch64::{_PREFETCH_LOCALITY3, _PREFETCH_WRITE};
    core::arch::aarch64::_prefetch::<_PREFETCH_WRITE, _PREFETCH_LOCALITY3>(ptr.cast());
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
unsafe fn prefetch_next_line(ptr: *const Mersenne31Field) {
    use core::arch::x86_64::{_mm_prefetch, _MM_HINT_ET0};
    _mm_prefetch(ptr as *const i8, _MM_HINT_ET0);
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
#[inline(always)]
unsafe fn prefetch_next_line(ptr: *const Mersenne31Field) {}

use std::time::Instant;
pub struct Timer {
    starting_time: Instant,
}

impl Timer {
    pub fn new() -> Self {
        Timer {
            starting_time: Instant::now(),
        }
    }

    pub fn measure_running_time(&mut self, message: &str) {
        let end_time = Instant::now();
        let duration = end_time - self.starting_time;
        println!("{}: {:?}", message, duration);
        self.starting_time = end_time;
    }
}
