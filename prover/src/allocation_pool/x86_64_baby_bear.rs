//! BabyBear (with its degree-4 extension) on x86-64.
//!
//! Two things are specific to this field on this target:
//!
//! * The block-padded codeword layout of the AVX-512 strided base LDE
//!   ([`PADDED_GEOMETRY`]): blocks of `2^14` base elements (64 KB, the
//!   cache-resident working set the gather sweep is tuned for) separated by
//!   64 unused elements (four cache lines), so the radix-1024 global pass
//!   streams through distinct L2 sets. Every data window starts 64-byte
//!   aligned for the kernels' streaming stores.
//! * The box placement rule. Measured on Zen 5 (EPYC 9B45, THP `always`):
//!   the same-size sumcheck's initial pass streams some 30 polys side by
//!   side, and its time depends on the *spacing* of the polys' mappings,
//!   i.e. on the box size. Exact-size boxes (glibc maps them back to back,
//!   4 KB apart modulo their size) run the `2^24` layer-1 pass in 97-106 ms;
//!   boxes over-allocated by 256 KB..4 MB take 220-233 ms (2.2x), while
//!   16 MB of over-allocation is fast again — the window's alignment, a
//!   per-poly stagger and its huge-page backing make no difference. So a
//!   box is exactly the request plus 64 bytes of alignment slack. Plain
//!   polys and padded codewords therefore sit in separate size classes
//!   (256 MB vs 257 MB for `2^24` extension polys and `2^26` codewords);
//!   that costs nothing here, since the codewords stay live through the
//!   whole GKR phase and the two sets are never interchangeable inside one
//!   proof. (Rounding the 257 MB codeword class up to a 16 MB multiple was
//!   measured too: tree building and WHIR are unchanged, so it is not done.)

use super::*;
use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

/// Block size of the padded layout (base elements): `2^14`.
pub const PADDED_BLOCK_LOG2: u32 = 14;
/// Unused elements between consecutive blocks.
pub const PADDED_BLOCK_PAD: usize = 64;
/// The padded layout this pool serves (the strided base LDE's output).
pub const PADDED_GEOMETRY: PaddedBlocks = PaddedBlocks {
    block_log2: PADDED_BLOCK_LOG2,
    pad: PADDED_BLOCK_PAD,
};
/// Alignment of every data window (bytes): the strided kernels' streaming
/// stores.
pub const WINDOW_ALIGN: usize = 64;

/// `POOL_TRACE=1` prints every allocation (element size, length, window
/// address) to stderr.
fn trace() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("POOL_TRACE").is_ok())
}

#[derive(Clone)]
pub struct X86BabyBearAllocationPool {
    store: Arc<RetainedStore>,
}

impl X86BabyBearAllocationPool {
    /// A retaining pool.
    pub fn new() -> Self {
        Self::with_retain(true)
    }
    /// `retain == false`: a trivial proxy of the global allocator.
    pub fn with_retain(retain: bool) -> Self {
        Self {
            store: Arc::new(RetainedStore::new(retain)),
        }
    }
    /// A proxy pool (nothing retained).
    pub fn proxy() -> Self {
        Self::with_retain(false)
    }
    /// Handles sharing one underlying pool.
    pub fn shares_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.store, &other.store)
    }

    /// Elements of the box that holds `requested_len` elements of `T`.
    fn box_len<T>(requested_len: usize) -> usize {
        let elem = core::mem::size_of::<T>();
        debug_assert!(WINDOW_ALIGN % elem == 0);
        (requested_len * elem + WINDOW_ALIGN) / elem
    }

    fn alloc<T>(&self, len: usize, layout: ColumnLayout) -> Buffer<T> {
        assert!(
            len.is_power_of_two() || len <= PADDED_GEOMETRY.block(),
            "pool requests are powers of two (got {len})"
        );
        if let ColumnLayout::PaddedBlocks(g) = layout {
            assert_eq!(
                g, PADDED_GEOMETRY,
                "this pool serves the strided base LDE's padded layout"
            );
        }
        let elem = core::mem::size_of::<T>();
        let requested_len = layout.storage_len(len);
        let n_alloc = Self::box_len::<T>(requested_len);
        let l = Layout::array::<MaybeUninit<T>>(n_alloc).unwrap();
        let ptr = self.store.alloc(l);
        let base = ptr.as_ptr() as usize;
        let aligned = base.div_ceil(WINDOW_ALIGN) * WINDOW_ALIGN;
        debug_assert!((aligned - base) % elem == 0);
        let offset = (aligned - base) / elem;
        debug_assert!(offset + requested_len <= n_alloc);
        if trace() {
            eprintln!(
                "[pool-trace] alloc elem {elem} len {len} {layout:?} -> window {aligned:#x} (mod 2MB {:#x}), box {base:#x} of {} bytes",
                aligned % (2 << 20),
                l.size()
            );
        }
        Buffer::from_parts(unsafe { box_from_raw(ptr, n_alloc) }, offset, requested_len)
    }

    fn give<T>(&self, buffer: Buffer<T>) {
        let (ptr, layout) = raw_from_box(buffer.into_box());
        self.store.give(ptr, layout);
    }
}

impl Default for X86BabyBearAllocationPool {
    fn default() -> Self {
        Self::new()
    }
}

impl AllocationPool<BabyBearField, BabyBearExt4> for X86BabyBearAllocationPool {
    fn alloc_base(&self, len: usize, layout: ColumnLayout) -> Buffer<BabyBearField> {
        self.alloc(len, layout)
    }
    fn alloc_ext(&self, len: usize, layout: ColumnLayout) -> Buffer<BabyBearExt4> {
        self.alloc(len, layout)
    }
    fn give_base(&self, buffer: Buffer<BabyBearField>) {
        self.give(buffer)
    }
    fn give_ext(&self, buffer: Buffer<BabyBearExt4>) {
        self.give(buffer)
    }
    fn alloc_raw(&self, layout: Layout) -> NonNull<u8> {
        self.store.alloc(layout)
    }
    fn give_raw(&self, ptr: NonNull<u8>, layout: Layout) {
        self.store.give(ptr, layout)
    }
    fn retained_raw(&self, layout: Layout) -> usize {
        self.store.retained(layout)
    }
    fn retains(&self) -> bool {
        self.store.retains()
    }
    fn stats(&self) -> PoolStats {
        self.store.stats()
    }
    fn share(&self) -> Arc<dyn AllocationPool<BabyBearField, BabyBearExt4>> {
        Arc::new(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn windows_are_aligned_and_exact() {
        let pool = X86BabyBearAllocationPool::new();
        let b = pool.alloc_ext(1 << 16, ColumnLayout::Contiguous);
        assert_eq!(b.len(), 1 << 16);
        assert_eq!(b.as_ptr() as usize % WINDOW_ALIGN, 0);
        let p = pool.alloc_base(1 << 20, ColumnLayout::PaddedBlocks(PADDED_GEOMETRY));
        assert_eq!(p.len(), PADDED_GEOMETRY.padded_len(1 << 20));
        assert_eq!(p.as_ptr() as usize % WINDOW_ALIGN, 0);
        // a small request is its size plus the alignment slack
        assert_eq!(
            X86BabyBearAllocationPool::box_len::<BabyBearExt4>(1 << 16),
            (1 << 16) + 4
        );
        // a padded 2^26 codeword: 257 MB plus the slack
        let padded = PADDED_GEOMETRY.padded_len(1 << 26);
        let bytes = X86BabyBearAllocationPool::box_len::<BabyBearField>(padded) * 4;
        assert_eq!(bytes, 257 * (1 << 20) + WINDOW_ALIGN);
        // a 2^24 extension poly: 256 MB plus the slack
        let bytes = X86BabyBearAllocationPool::box_len::<BabyBearExt4>(1 << 24) * 16;
        assert_eq!(bytes, 256 * (1 << 20) + WINDOW_ALIGN);
        pool.give_ext(b);
        pool.give_base(p);
    }

    /// The pool-less prover entries and the setup commit resolve to THIS pool
    /// for the BabyBear pair (retaining and proxy flavours alike), so every
    /// padded request has the 64-byte window the strided base LDE needs.
    #[test]
    fn default_pools_for_baby_bear_are_aligned() {
        for pool in [
            crate::allocation_pool::default_pool_for::<BabyBearField, BabyBearExt4>(),
            crate::allocation_pool::default_proxy_pool_for::<BabyBearField, BabyBearExt4>(),
        ] {
            let p = pool.alloc_base(1 << 20, ColumnLayout::PaddedBlocks(PADDED_GEOMETRY));
            assert_eq!(p.len(), PADDED_GEOMETRY.padded_len(1 << 20));
            assert_eq!(p.as_ptr() as usize % WINDOW_ALIGN, 0);
            pool.give_base(p);
        }
    }

    #[test]
    fn same_layout_reuses_records() {
        let pool = X86BabyBearAllocationPool::new();
        let b = pool.alloc_ext(1 << 12, ColumnLayout::Contiguous);
        let p = b.as_ptr() as usize;
        pool.give_ext(b);
        let c = pool.alloc_ext(1 << 12, ColumnLayout::Contiguous);
        assert_eq!(c.as_ptr() as usize, p, "same layout reuses the record");
        assert_eq!(pool.stats().hits, 1);
        // 4 base elements per extension element: same bytes, but the element
        // alignment differs, so a different record
        let f = pool.alloc_base(1 << 14, ColumnLayout::Contiguous);
        assert_eq!(pool.stats().misses, 2);
        pool.give_ext(c);
        pool.give_base(f);
        let proxy = X86BabyBearAllocationPool::proxy();
        let c = proxy.alloc_ext(1 << 12, ColumnLayout::Contiguous);
        proxy.give_ext(c);
        assert_eq!(proxy.stats().retained_bytes, 0);
    }
}
