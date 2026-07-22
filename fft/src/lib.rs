#![feature(allocator_api)]
#![feature(slice_swap_unchecked)]

pub mod column_major;
pub mod field_utils;
pub mod twiddles;
pub mod utils;

pub use self::column_major::*;
pub use self::field_utils::*;
pub use self::twiddles::*;
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
    assert!(core::mem::size_of::<u32>() >= core::mem::align_of::<u32>());

    CACHE_LINE_WIDTH / core::mem::size_of::<u32>()
};

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
