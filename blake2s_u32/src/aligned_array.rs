use core::fmt;
use core::hash::Hash;
use core::ops::{Deref, DerefMut};

#[repr(C)]
pub struct AlignedArray<T, A, const N: usize> {
    _aligner: [A; 0],
    data: [T; N],
}

#[repr(C)]
pub struct AlignedSlice<T, A> {
    _aligner: [A; 0],
    data: [T],
}

#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct A64;

pub type AlignedArray64<T, const N: usize> = AlignedArray<T, A64, N>;
pub type AlignedSlice64<T> = AlignedSlice<T, A64>;

impl<T, A, const N: usize> AlignedArray<T, A, N> {
    #[inline(always)]
    pub const fn deref_mut_impl(&mut self) -> &mut [T; N] {
        &mut self.data
    }
}

impl<T, A> AlignedSlice<T, A> {
    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn as_ptr(&self) -> *const T {
        self.data.as_ptr()
    }

    /// # SAFETY
    /// Same as `core::slice::from_raw_parts`,
    /// but caller should also ensure data is aligned for type `A` (not just `T`!)
    #[inline(always)]
    pub const unsafe fn from_raw_parts<'a>(data: *const T, len: usize) -> &'a Self {
        &*(core::ptr::slice_from_raw_parts(data, len) as *const Self)
    }
}

impl<T, A, const N: usize> Deref for AlignedArray<T, A, N> {
    type Target = [T; N];

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T, A, const N: usize> DerefMut for AlignedArray<T, A, N> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.deref_mut_impl()
    }
}

impl<T: Clone, A, const N: usize> Clone for AlignedArray<T, A, N> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            _aligner: [],
            data: self.data.clone(),
        }
    }
}

impl<T: Copy, A: Copy, const N: usize> Copy for AlignedArray<T, A, N> {}

impl<T: fmt::Debug, A, const N: usize> fmt::Debug for AlignedArray<T, A, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.data, f)
    }
}

impl<T: Hash, A, const N: usize> Hash for AlignedArray<T, A, N> {
    #[inline(always)]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.data.hash(state);
    }
}
