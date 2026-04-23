use core::mem::MaybeUninit;

#[derive(Clone, Debug)]
#[repr(C)]
pub struct LazyVec<V: Copy, const N: usize> {
    data: [MaybeUninit<V>; N],
    len: usize,
}

impl<V: Copy, const N: usize> LazyVec<V, N> {
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            data: [const { MaybeUninit::uninit() }; N],
            len: 0,
        }
    }

    #[inline(always)]
    pub fn push(&mut self, val: V) {
        debug_assert!(self.len < N);
        unsafe {
            self.data.get_unchecked_mut(self.len).write(val);
        }
        self.len += 1;
    }

    #[inline(always)]
    pub fn get(&self, idx: usize) -> &V {
        debug_assert!(idx < self.len);
        unsafe { self.data.get_unchecked(idx).assume_init_ref() }
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[V] {
        unsafe { core::slice::from_raw_parts(self.data.as_ptr().cast::<V>(), self.len) }
    }

    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [V] {
        unsafe { core::slice::from_raw_parts_mut(self.data.as_mut_ptr().cast::<V>(), self.len) }
    }

    #[inline(always)]
    pub const fn clear(&mut self) {
        self.len = 0;
    }

    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline(always)]
    pub unsafe fn get_unchecked(&self, idx: usize) -> &V {
        debug_assert!(idx < N);
        self.data.get_unchecked(idx).assume_init_ref()
    }

    #[inline(always)]
    pub unsafe fn get_unchecked_mut(&mut self, idx: usize) -> &mut V {
        debug_assert!(idx < N);
        self.data.get_unchecked_mut(idx).assume_init_mut()
    }

    #[inline(always)]
    pub unsafe fn set_unchecked(&mut self, idx: usize, val: V) {
        debug_assert!(idx < N);
        self.data.get_unchecked_mut(idx).write(val);
    }

    #[inline(always)]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= N);
        self.len = new_len;
    }

    #[inline(always)]
    pub unsafe fn into_array(self) -> [V; N] {
        debug_assert!(self.len == N);
        // MaybeUninit::array_assume_init(self.data)
        unsafe { self.data.map(|el| el.assume_init()) }
    }

    /// Returns a reference to the first M elements as a fixed-size array.
    /// The caller must ensure at least M elements have been written.
    #[inline(always)]
    pub unsafe fn as_array<const M: usize>(&self) -> &[V; M] {
        debug_assert!(M <= N);
        debug_assert!(self.len >= M);
        &*self.data.as_ptr().cast::<[V; M]>()
    }

    /// Returns a mutable reference to the first M elements as a fixed-size array.
    /// The caller must ensure at least M elements have been written.
    #[inline(always)]
    pub unsafe fn as_array_mut<const M: usize>(&mut self) -> &mut [V; M] {
        debug_assert!(M <= N);
        debug_assert!(self.len >= M);
        &mut *self.data.as_mut_ptr().cast::<[V; M]>()
    }
}
