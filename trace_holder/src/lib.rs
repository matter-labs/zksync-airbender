#![feature(allocator_api)]

use field::Mersenne31Field;
use std::alloc::Allocator;
use worker::Worker;

// Can be initialized via zeroing + synonym of "no-drop"
pub trait Zeroable: Sized + 'static + Clone + Copy {}

impl Zeroable for Mersenne31Field {}
impl Zeroable for u32 {}
impl Zeroable for usize {}
impl Zeroable for u64 {}
impl Zeroable for (u32, u32) {}

const _: () = const {
    assert!(core::mem::size_of::<(u32, u32)>() >= core::mem::align_of::<(u32, u32)>());
    assert!(core::mem::size_of::<(u32, u32)>() == 8);
};

#[derive(Clone, Copy, Debug)]
#[repr(align(16384))] // up to M1 family paging
struct Aligner {
    _inner: [u8; PAGE_SIZE],
}

const VERBOSE: bool = false;

pub const PAGE_SIZE: usize = 16384;

pub mod column_major;
pub mod row_major;

pub use self::column_major::*;
pub use self::row_major::*;

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

/// This trait
pub unsafe trait ColumnMajorTraceStorage<T: 'static + Sized + Send + Sync + Clone + Copy> {
    fn start(&self) -> SendSyncPtrWrapper<T>;
    fn width(&self) -> usize;
    fn len(&self) -> usize;
    fn as_slice(&self) -> &[T] {
        unsafe {
            core::slice::from_raw_parts(self.start().0.cast_const(), self.width() * self.len())
        }
    }

    fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.start().0, self.width() * self.len()) }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SendSyncPtrWrapper<T: 'static + Sized + Send + Sync + Clone + Copy>(pub *mut T);

unsafe impl<T: 'static + Sized + Send + Sync + Clone + Copy> Send for SendSyncPtrWrapper<T> {}
unsafe impl<T: 'static + Sized + Send + Sync + Clone + Copy> Sync for SendSyncPtrWrapper<T> {}
