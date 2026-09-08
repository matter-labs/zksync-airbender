//! Cross-proof allocation pool for the prover's large power-of-two buffers
//! (GKR polys, RS codewords, fold scratch), typed by the prover's field pair.
//!
//! [`AllocationPool<F, E>`] is the trait the prover allocates through — the
//! prover, `Backend` and `GKRBackend` signatures take
//! `&dyn AllocationPool<F, E>` — and, like the FFT backends, the placement
//! policy lives in per-field / per-target implementations:
//!
//! * [`GenericAllocationPool<F, E>`] (`generic.rs`): exact contiguous boxes
//!   for any field on any target — the macOS / aarch64 pool, and the pool
//!   the pool-less prover entries create on every target.
//! * [`X86BabyBearAllocationPool`] (`x86_64_baby_bear.rs`): BabyBear on
//!   x86-64 — the block-padded codeword layout of the AVX-512 strided base
//!   LDE ([`x86_64_baby_bear::PADDED_GEOMETRY`], blocks of `2^14` field
//!   elements) plus the box placement rule measured on Zen 5.
//! * [`X86Proth120AllocationPool`] (`x86_64_proth120.rs`): Proth120 on
//!   x86-64, trivial contiguous allocations for now.
//!
//! Every pool hands out [`Buffer`]s exposing exactly the requested (padded)
//! length, retains returned memory by its allocation layout for the next
//! proof unless built in proxy mode (then it is a trivial proxy of the
//! global allocator), and is a cheap-to-clone handle with interior locking,
//! so one pool can serve proofs running in parallel
//! ([`AllocationPool::share`]).

use core::alloc::Layout;
use core::mem::MaybeUninit;
use core::ptr::NonNull;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

pub mod generic;
pub use generic::GenericAllocationPool;
#[cfg(target_arch = "x86_64")]
pub mod x86_64_baby_bear;
#[cfg(target_arch = "x86_64")]
pub use x86_64_baby_bear::X86BabyBearAllocationPool;
#[cfg(target_arch = "x86_64")]
pub mod x86_64_proth120;
#[cfg(target_arch = "x86_64")]
pub use x86_64_proth120::X86Proth120AllocationPool;

/// The BabyBear pool of this target.
#[cfg(target_arch = "x86_64")]
pub type DefaultBabyBearAllocationPool = X86BabyBearAllocationPool;
/// The BabyBear pool of this target.
#[cfg(not(target_arch = "x86_64"))]
pub type DefaultBabyBearAllocationPool = GenericAllocationPool<
    field::baby_bear::base::BabyBearField,
    field::baby_bear::ext4::BabyBearExt4,
>;
/// The Proth120 pool of this target.
#[cfg(target_arch = "x86_64")]
pub type DefaultProth120AllocationPool = X86Proth120AllocationPool;
/// The Proth120 pool of this target.
#[cfg(not(target_arch = "x86_64"))]
pub type DefaultProth120AllocationPool = GenericAllocationPool<field::Proth120, field::Proth120>;

/// The pool a pool-less prover entry uses for the field pair it runs on:
/// the target's BabyBear / Proth120 pool when `(F, E)` is one of those pairs
/// (an `Any` downcast of the shared handle — the pools are concrete types,
/// the entries generic), else a [`GenericAllocationPool`].
pub fn default_pool_for<F: 'static, E: 'static>() -> Arc<dyn AllocationPool<F, E>> {
    use core::any::Any;
    let candidates: [Box<dyn Any>; 2] = [
        Box::new(DefaultBabyBearAllocationPool::new().share()),
        Box::new(DefaultProth120AllocationPool::new().share()),
    ];
    for c in candidates {
        if let Ok(p) = c.downcast::<Arc<dyn AllocationPool<F, E>>>() {
            return *p;
        }
    }
    GenericAllocationPool::<F, E>::new().share()
}

/// Base page size of the target: 16 KB on Apple Silicon macOS, 4 KB
/// elsewhere (Linux x86-64 and aarch64 server kernels).
pub const PAGE: usize = if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
    16 << 10
} else {
    4096
};
/// Cache line of the target (128 B on Apple M-series, 64 B elsewhere).
pub const CACHE_LINE: usize = if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
    128
} else {
    64
};
/// Transparent huge page of the target where the kernel provides them
/// (Linux, 2 MB); macOS has none, so its "huge" granule is the page.
pub const HUGE_PAGE: usize = if cfg!(target_os = "linux") {
    2 << 20
} else {
    PAGE
};

/// Geometry of a block-padded FFT output layout: blocks of `2^block_log2`
/// elements with `pad` unused elements between consecutive blocks (so the
/// global FFT passes do not stream through one set of L2 lines). Which
/// geometry a pool serves is the pool's business: it is a property of the
/// field and of the machine's caches.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PaddedBlocks {
    pub block_log2: u32,
    pub pad: usize,
}

impl PaddedBlocks {
    /// Elements per block.
    pub const fn block(self) -> usize {
        1 << self.block_log2
    }
    /// Distance between the starts of consecutive blocks (elements).
    pub const fn stride(self) -> usize {
        (1 << self.block_log2) + self.pad
    }
    /// Storage length of `len` natural elements: `len` when it fits one
    /// block, else `blocks * stride` (the trailing pad of the last block
    /// included, so every block has the same stride).
    pub const fn padded_len(self, len: usize) -> usize {
        if len <= self.block() {
            len
        } else {
            (len >> self.block_log2) * self.stride()
        }
    }
    /// Storage position of natural index `i`.
    #[inline(always)]
    pub const fn index(self, i: usize) -> usize {
        (i >> self.block_log2) * self.stride() + (i & (self.block() - 1))
    }
    /// Natural length of a column stored in `storage_len` elements.
    pub const fn natural_len(self, storage_len: usize) -> usize {
        if storage_len >= self.stride() {
            (storage_len / self.stride()) << self.block_log2
        } else {
            storage_len
        }
    }
}

/// How a coset column is laid out in its storage — also the shape of a
/// pool request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColumnLayout {
    /// Natural order, one contiguous slice.
    Contiguous,
    /// Block-padded (an FFT output): the gaps between blocks are never read.
    PaddedBlocks(PaddedBlocks),
}

impl ColumnLayout {
    /// Storage elements for `natural_len` values.
    pub const fn storage_len(self, natural_len: usize) -> usize {
        match self {
            Self::Contiguous => natural_len,
            Self::PaddedBlocks(g) => g.padded_len(natural_len),
        }
    }
    /// Natural length of a column stored in `storage_len` elements.
    pub const fn natural_len(self, storage_len: usize) -> usize {
        match self {
            Self::Contiguous => storage_len,
            Self::PaddedBlocks(g) => g.natural_len(storage_len),
        }
    }
    /// Storage position of natural index `i`.
    #[inline(always)]
    pub const fn index(self, i: usize) -> usize {
        match self {
            Self::Contiguous => i,
            Self::PaddedBlocks(g) => g.index(i),
        }
    }
}

/// A pooled buffer: the data window of `inner` exposes exactly
/// `requested_len` elements (the pool may have placed it at an offset for
/// alignment, and the box may be larger).
pub struct Buffer<T> {
    inner: Box<[MaybeUninit<T>]>,
    offset: usize,
    requested_len: usize,
}

impl<T> Buffer<T> {
    pub(crate) fn from_parts(
        inner: Box<[MaybeUninit<T>]>,
        offset: usize,
        requested_len: usize,
    ) -> Self {
        debug_assert!(offset + requested_len <= inner.len());
        Self {
            inner,
            offset,
            requested_len,
        }
    }
    /// The whole box (for returning it to the pool that made it).
    pub(crate) fn into_box(self) -> Box<[MaybeUninit<T>]> {
        self.inner
    }
    /// The requested length.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.requested_len
    }
    #[inline(always)]
    pub fn as_ref(&self) -> &[MaybeUninit<T>] {
        &self.inner[self.offset..self.offset + self.requested_len]
    }
    #[inline(always)]
    pub fn as_mut(&mut self) -> &mut [MaybeUninit<T>] {
        &mut self.inner[self.offset..self.offset + self.requested_len]
    }
    /// The window as initialized values.
    ///
    /// # Safety
    /// Every one of the `requested_len` elements must have been written.
    #[inline(always)]
    pub unsafe fn as_ref_assume_init(&self) -> &[T] {
        core::slice::from_raw_parts(self.as_ref().as_ptr() as *const T, self.requested_len)
    }
    /// # Safety
    /// Same as [`Self::as_ref_assume_init`].
    #[inline(always)]
    pub unsafe fn as_mut_assume_init(&mut self) -> &mut [T] {
        core::slice::from_raw_parts_mut(self.as_mut().as_mut_ptr() as *mut T, self.requested_len)
    }
    #[inline(always)]
    pub fn as_ptr(&self) -> *const T {
        self.as_ref().as_ptr() as *const T
    }
    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.as_mut().as_mut_ptr() as *mut T
    }
    /// Alignment of the window start (bytes).
    pub fn alignment(&self) -> usize {
        let p = self.as_ptr() as usize;
        1 << p.trailing_zeros().min(63)
    }
    /// Shrink the exposed length (e.g. a padded request used plain).
    pub fn truncate(&mut self, len: usize) {
        assert!(len <= self.requested_len);
        self.requested_len = len;
    }
}

/// Storage of a prover poly: a plain owned slice or a pooled buffer that
/// is returned to its pool when the owner is done.
pub enum AllocationType<T> {
    Owned(Box<[T]>),
    Pooled(Buffer<T>),
}

impl<T> AllocationType<T> {
    /// A pooled buffer whose window is fully initialized.
    ///
    /// # Safety
    /// Every element of the window must have been written.
    pub unsafe fn from_initialized(buffer: Buffer<T>) -> Self {
        Self::Pooled(buffer)
    }
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        match self {
            Self::Owned(b) => b,
            Self::Pooled(buf) => unsafe { buf.as_ref_assume_init() },
        }
    }
    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        match self {
            Self::Owned(b) => b,
            Self::Pooled(buf) => unsafe { buf.as_mut_assume_init() },
        }
    }
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.as_slice().len()
    }
    /// Give a pooled base-field buffer back; owned slices are dropped.
    pub fn release_base<E>(self, pool: &dyn AllocationPool<T, E>) {
        match self {
            Self::Owned(_) => {}
            Self::Pooled(buf) => pool.give_base(buf),
        }
    }
    /// Give a pooled extension-field buffer back; owned slices are dropped.
    pub fn release_ext<F>(self, pool: &dyn AllocationPool<F, T>) {
        match self {
            Self::Owned(_) => {}
            Self::Pooled(buf) => pool.give_ext(buf),
        }
    }
}

impl<T> core::ops::Deref for AllocationType<T> {
    type Target = [T];
    #[inline(always)]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> core::ops::DerefMut for AllocationType<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> From<Box<[T]>> for AllocationType<T> {
    fn from(b: Box<[T]>) -> Self {
        Self::Owned(b)
    }
}

impl<T> From<Vec<T>> for AllocationType<T> {
    fn from(v: Vec<T>) -> Self {
        Self::Owned(v.into_boxed_slice())
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for AllocationType<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Owned(b) => f.debug_tuple("Owned").field(&b.len()).finish(),
            Self::Pooled(b) => f.debug_tuple("Pooled").field(&b.len()).finish(),
        }
    }
}

/// Cumulative counters of a pool.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PoolStats {
    /// requests served from retained memory
    pub hits: usize,
    /// requests that went to the global allocator
    pub misses: usize,
    /// bytes retained right now
    pub retained_bytes: usize,
}

/// The prover's allocation interface for the field pair `(F, E)`. Every
/// method takes `&self`: implementations lock internally.
pub trait AllocationPool<F, E>: Send + Sync {
    /// `len` base elements (a power of two, or fewer than one padded block)
    /// in `layout`; the buffer exposes `layout.storage_len(len)` elements.
    fn alloc_base(&self, len: usize, layout: ColumnLayout) -> Buffer<F>;
    /// `len` extension elements, as [`Self::alloc_base`].
    fn alloc_ext(&self, len: usize, layout: ColumnLayout) -> Buffer<E>;
    /// Return a buffer (retained, or freed in proxy mode).
    fn give_base(&self, buffer: Buffer<F>);
    /// Return a buffer (retained, or freed in proxy mode).
    fn give_ext(&self, buffer: Buffer<E>);
    /// Raw memory of exactly `layout` (the scratch-box flavour, see
    /// `alloc_box`), retained by its layout when returned.
    fn alloc_raw(&self, layout: Layout) -> NonNull<u8>;
    /// Return memory from [`Self::alloc_raw`] (or any global allocation of
    /// that layout).
    fn give_raw(&self, ptr: NonNull<u8>, layout: Layout);
    /// Retained raw records of this layout.
    fn retained_raw(&self, layout: Layout) -> usize;
    /// `false` for a proxy of the global allocator.
    fn retains(&self) -> bool;
    fn stats(&self) -> PoolStats;
    /// A handle to the same pool for another thread (the detached oracle
    /// release, a second prover).
    fn share(&self) -> Arc<dyn AllocationPool<F, E>>;
}

impl<F, E> dyn AllocationPool<F, E> + '_ {
    /// A plain `Box<[MaybeUninit<T>]>` of exactly `len` elements (the fold
    /// scratch flavour: exact length, no alignment window), retained by its
    /// layout.
    pub fn alloc_box<T>(&self, len: usize) -> Box<[MaybeUninit<T>]> {
        let layout = Layout::array::<MaybeUninit<T>>(len).unwrap();
        if layout.size() == 0 {
            return Box::new_uninit_slice(len);
        }
        let ptr = self.alloc_raw(layout);
        unsafe { box_from_raw(ptr, len) }
    }

    /// Return a box from [`Self::alloc_box`] (or any plain box: the layout
    /// is what is retained).
    pub fn give_box<T>(&self, b: Box<[MaybeUninit<T>]>) {
        let (ptr, layout) = raw_from_box(b);
        if layout.size() == 0 {
            return;
        }
        self.give_raw(ptr, layout);
    }

    /// Make sure `count` boxes of `len` elements are retained and
    /// page-touched (top-up: only the shortfall is allocated). No-op in
    /// proxy mode.
    pub fn prefill_boxes<T>(&self, len: usize, count: usize, worker: &worker::Worker) {
        if !self.retains() {
            return;
        }
        let layout = Layout::array::<MaybeUninit<T>>(len).unwrap();
        if layout.size() == 0 {
            return;
        }
        let have = self.retained_raw(layout);
        if have >= count {
            return;
        }
        let fresh: Vec<Box<[MaybeUninit<T>]>> = (0..count - have)
            .map(|_| Box::new_uninit_slice(len))
            .collect();
        let pages: Vec<(usize, usize)> = fresh
            .iter()
            .map(|b| (b.as_ptr() as usize, layout.size()))
            .collect();
        touch_pages(&pages, worker);
        for b in fresh {
            self.give_box(b);
        }
    }
}

/// A retained allocation, type-erased: the box it came from is rebuilt for
/// any element type of the same layout.
struct RawAlloc {
    ptr: NonNull<u8>,
    layout: Layout,
}

unsafe impl Send for RawAlloc {}

/// Type-erased retained records keyed by allocation layout, shared by the
/// pool implementations (each decides which layouts it asks for).
pub(crate) struct RetainedStore {
    retain: bool,
    free: Mutex<BTreeMap<(usize, usize), Vec<RawAlloc>>>,
    stats: Mutex<PoolStats>,
}

impl RetainedStore {
    pub(crate) fn new(retain: bool) -> Self {
        Self {
            retain,
            free: Mutex::new(BTreeMap::new()),
            stats: Mutex::new(PoolStats::default()),
        }
    }
    pub(crate) fn retains(&self) -> bool {
        self.retain
    }
    pub(crate) fn stats(&self) -> PoolStats {
        *self.stats.lock().unwrap()
    }
    /// A retained record of `layout`, or a fresh global allocation.
    pub(crate) fn alloc(&self, layout: Layout) -> NonNull<u8> {
        assert!(
            layout.size() > 0,
            "zero-size pool requests are the caller's business"
        );
        let key = (layout.size(), layout.align());
        let recycled = self
            .free
            .lock()
            .unwrap()
            .get_mut(&key)
            .and_then(|v| v.pop());
        match recycled {
            Some(raw) => {
                debug_assert_eq!(raw.layout, layout);
                let mut s = self.stats.lock().unwrap();
                s.hits += 1;
                s.retained_bytes -= layout.size();
                raw.ptr
            }
            None => {
                self.stats.lock().unwrap().misses += 1;
                let p = unsafe { std::alloc::alloc(layout) };
                NonNull::new(p).unwrap_or_else(|| std::alloc::handle_alloc_error(layout))
            }
        }
    }
    /// Retain (or free, in proxy mode) an allocation of `layout`.
    pub(crate) fn give(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() == 0 {
            return;
        }
        if !self.retain {
            unsafe { std::alloc::dealloc(ptr.as_ptr(), layout) };
            return;
        }
        self.stats.lock().unwrap().retained_bytes += layout.size();
        self.free
            .lock()
            .unwrap()
            .entry((layout.size(), layout.align()))
            .or_default()
            .push(RawAlloc { ptr, layout });
    }
    pub(crate) fn retained(&self, layout: Layout) -> usize {
        self.free
            .lock()
            .unwrap()
            .get(&(layout.size(), layout.align()))
            .map(|v| v.len())
            .unwrap_or(0)
    }
}

impl Drop for RetainedStore {
    fn drop(&mut self) {
        let free = core::mem::take(&mut *self.free.lock().unwrap());
        for (_, v) in free {
            for raw in v {
                unsafe { std::alloc::dealloc(raw.ptr.as_ptr(), raw.layout) };
            }
        }
    }
}

/// Rebuild the box of `len` elements that `ptr` was allocated for.
///
/// # Safety
/// `ptr` must come from the global allocator with
/// `Layout::array::<MaybeUninit<T>>(len)`.
pub(crate) unsafe fn box_from_raw<T>(ptr: NonNull<u8>, len: usize) -> Box<[MaybeUninit<T>]> {
    Box::from_raw(core::ptr::slice_from_raw_parts_mut(
        ptr.as_ptr() as *mut MaybeUninit<T>,
        len,
    ))
}

/// Take a box apart into its allocation and layout.
pub(crate) fn raw_from_box<T>(b: Box<[MaybeUninit<T>]>) -> (NonNull<u8>, Layout) {
    let layout = Layout::for_value::<[MaybeUninit<T>]>(&b);
    let ptr = Box::into_raw(b) as *mut MaybeUninit<T> as *mut u8;
    (NonNull::new(ptr).unwrap(), layout)
}

/// One write per page of every `(ptr, bytes)` range, split over the worker,
/// so fresh memory pays its page faults here rather than in the first
/// kernel that streams through it.
pub(crate) fn touch_pages(pages: &[(usize, usize)], worker: &worker::Worker) {
    if pages.is_empty() {
        return;
    }
    let total_pages: usize = pages.iter().map(|(_, bytes)| bytes.div_ceil(PAGE)).sum();
    worker.scope(total_pages, |scope, geometry| {
        for idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(idx);
            let size = geometry.get_chunk_size(idx);
            worker::Worker::smart_spawn(scope, idx == geometry.len() - 1, move |_| {
                // page p of the concatenation of all ranges
                let mut p = 0usize;
                for &(ptr, bytes) in pages.iter() {
                    let n = bytes.div_ceil(PAGE);
                    let lo = start.max(p);
                    let hi = (start + size).min(p + n);
                    for page in lo..hi {
                        let off = (page - p) * PAGE;
                        unsafe {
                            core::ptr::write_volatile((ptr + off) as *mut u8, 0);
                        }
                    }
                    p += n;
                }
            });
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    const G: PaddedBlocks = PaddedBlocks {
        block_log2: 14,
        pad: 64,
    };

    #[test]
    fn padded_layout_math() {
        assert_eq!(G.stride(), (1 << 14) + 64);
        assert_eq!(G.padded_len(1 << 12), 1 << 12);
        assert_eq!(G.padded_len(1 << 14), 1 << 14);
        assert_eq!(G.padded_len(1 << 16), 4 * G.stride());
        assert_eq!(G.index(5), 5);
        assert_eq!(G.index((1 << 14) + 3), G.stride() + 3);
        assert_eq!(G.natural_len(G.padded_len(1 << 20)), 1 << 20);
        let l = ColumnLayout::PaddedBlocks(G);
        assert_eq!(l.storage_len(1 << 16), 4 * G.stride());
        assert_eq!(l.natural_len(4 * G.stride()), 1 << 16);
        assert_eq!(ColumnLayout::Contiguous.index(77), 77);
    }

    #[test]
    fn generic_pool_exact_len_and_retention() {
        let pool = GenericAllocationPool::<u32, [u32; 4]>::new();
        let dyn_pool: &dyn AllocationPool<u32, [u32; 4]> = &pool;
        let b = dyn_pool.alloc_base(1 << 16, ColumnLayout::Contiguous);
        assert_eq!(b.len(), 1 << 16);
        assert_eq!(b.as_ref().len(), 1 << 16);
        let p = b.as_ptr() as usize;
        dyn_pool.give_base(b);
        assert_eq!(dyn_pool.stats().retained_bytes, 4 << 16);
        let c = dyn_pool.alloc_base(1 << 16, ColumnLayout::Contiguous);
        assert_eq!(c.as_ptr() as usize, p, "same layout reuses the record");
        assert_eq!(dyn_pool.stats().hits, 1);
        // the padded request of a generic pool is just a longer box
        let d = dyn_pool.alloc_ext(1 << 16, ColumnLayout::PaddedBlocks(G));
        assert_eq!(d.len(), G.padded_len(1 << 16));
        dyn_pool.give_ext(d);
        dyn_pool.give_base(c);
        // scratch boxes go through the same store
        let bx = dyn_pool.alloc_box::<[u32; 4]>(1 << 10);
        assert_eq!(bx.len(), 1 << 10);
        dyn_pool.give_box(bx);
        assert_eq!(
            dyn_pool.retained_raw(Layout::array::<MaybeUninit<[u32; 4]>>(1 << 10).unwrap()),
            1
        );
        let shared = dyn_pool.share();
        assert_eq!(shared.stats(), dyn_pool.stats());
    }

    #[test]
    fn default_pool_selection() {
        let bb = default_pool_for::<
            field::baby_bear::base::BabyBearField,
            field::baby_bear::ext4::BabyBearExt4,
        >();
        let b = bb.alloc_base(1 << 16, ColumnLayout::Contiguous);
        #[cfg(target_arch = "x86_64")]
        assert_eq!(
            b.as_ptr() as usize % 64,
            0,
            "the x86 BabyBear pool aligns windows"
        );
        bb.give_base(b);
        let p = default_pool_for::<field::Proth120, field::Proth120>();
        let q = p.alloc_ext(1 << 10, ColumnLayout::Contiguous);
        assert_eq!(q.len(), 1 << 10);
        p.give_ext(q);
        let g = default_pool_for::<u32, [u32; 4]>();
        assert!(g.retains());
    }

    #[test]
    fn proxy_mode_retains_nothing() {
        let pool = GenericAllocationPool::<u32, [u32; 4]>::proxy();
        let b = pool.alloc_base(1 << 16, ColumnLayout::Contiguous);
        pool.give_base(b);
        assert_eq!(pool.stats().retained_bytes, 0);
        let c = pool.alloc_base(1 << 16, ColumnLayout::Contiguous);
        assert_eq!(
            pool.stats(),
            PoolStats {
                hits: 0,
                misses: 2,
                retained_bytes: 0
            }
        );
        assert!(!pool.retains());
        drop(c);
    }

    #[test]
    fn allocation_type_round_trip() {
        let pool = GenericAllocationPool::<u32, [u32; 4]>::new();
        let mut b = pool.alloc_ext(8, ColumnLayout::Contiguous);
        for (i, x) in b.as_mut().iter_mut().enumerate() {
            x.write([i as u32; 4]);
        }
        let a = unsafe { AllocationType::from_initialized(b) };
        assert_eq!(a.len(), 8);
        assert_eq!(a[3], [3; 4]);
        a.release_ext(&pool);
        assert_eq!(pool.stats().retained_bytes, 8 * 16);
        let owned: AllocationType<u32> = vec![1u32, 2, 3].into();
        assert_eq!(&*owned, &[1, 2, 3]);
        owned.release_base(&pool);
    }
}
