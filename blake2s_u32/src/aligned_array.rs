use core::fmt;
use core::hash::Hash;
use core::mem::MaybeUninit;
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
    pub fn from_value(value: T) -> Self
    where
        T: Copy,
    {
        Self {
            _aligner: [],
            data: [value; N],
        }
    }

    #[inline(always)]
    pub fn as_chunks<'a, const M: usize>(&'a self) -> &'a [AlignedArray<T, A, M>] {
        assert!(M > 0);
        assert_eq!(N % M, 0);
        assert_eq!(core::mem::size_of::<T>() * M, core::mem::align_of::<A>());
        unsafe {
            let len = N / M;
            core::slice::from_raw_parts(self.data.as_ptr().cast(), len)
        }
    }

    #[inline(always)]
    pub fn new_uninit() -> AlignedArray<MaybeUninit<T>, A, N> {
        AlignedArray {
            _aligner: [],
            data: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }

    #[inline(always)]
    pub const fn deref_mut_impl(&mut self) -> &mut [T; N] {
        &mut self.data
    }

    /// Reinterpret a region of the buffer starting at element `offset` as a
    /// slice of `count` elements of type `U`.
    ///
    /// # Safety
    /// The caller must ensure that the region is valid and that alignment/layout
    /// of `U` is compatible with the underlying `T` data.
    #[inline(always)]
    pub unsafe fn transmute_subslice<U>(&self, offset: usize, count: usize) -> &[U] {
        let ptr = self.data.as_ptr().add(offset).cast::<U>();
        debug_assert!(
            (ptr as usize).is_multiple_of(core::mem::align_of::<U>()),
            "transmute_subslice: pointer not aligned for target type"
        );
        core::slice::from_raw_parts(ptr, count)
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

impl<T, A, const N: usize> AlignedArray<MaybeUninit<T>, A, N> {
    #[inline(always)]
    pub unsafe fn assume_init_ref(&self) -> &AlignedArray<T, A, N> {
        &*(self as *const Self).cast::<AlignedArray<T, A, N>>()
    }

    #[inline(always)]
    pub fn write(&mut self, index: usize, value: T) {
        self.data[index].write(value);
    }

    #[inline(always)]
    pub fn copy_from_slice(&mut self, offset: usize, src: &[T])
    where
        T: Copy,
    {
        debug_assert!(offset + src.len() <= N);
        unsafe {
            core::ptr::copy_nonoverlapping(
                src.as_ptr(),
                self.data.as_mut_ptr().add(offset).cast::<T>(),
                src.len(),
            );
        }
    }

    /// Zero-fill slots `start..end`.
    #[inline(always)]
    pub unsafe fn zero_range(&mut self, start: usize, end: usize) {
        debug_assert!(end <= N);
        let ptr = self.data.as_mut_ptr();
        let mut i = start;
        while i < end {
            core::ptr::write_volatile(ptr.add(i), MaybeUninit::zeroed());
            i += 1;
        }
    }

    /// Reinterpret the first `M` elements as an initialized `AlignedArray<T, A, M>`.
    ///
    /// # Safety
    /// The caller must ensure that elements `0..M` have been initialized.
    #[inline(always)]
    pub unsafe fn assume_init_subarray<const M: usize>(&self) -> &AlignedArray<T, A, M> {
        debug_assert!(M <= N);
        &*(self as *const Self).cast::<AlignedArray<T, A, M>>()
    }

    /// Mutable version of `assume_init_subarray`.
    ///
    /// # Safety
    /// The caller must ensure that elements `0..M` have been initialized.
    #[inline(always)]
    pub unsafe fn assume_init_subarray_mut<const M: usize>(
        &mut self,
    ) -> &mut AlignedArray<T, A, M> {
        debug_assert!(M <= N);
        &mut *(self as *mut Self).cast::<AlignedArray<T, A, M>>()
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
