//! Ordinary host storage for the CPU backend: one finite trace block, guest RAM
//! and one JIT trace chunk.
//!
//! The property the shared producer accounting depends on is that a block is a
//! *credit*: it owns exactly one fixed-size allocation and refuses to serve
//! more than it has.

use execution_prover_model::allocator::HostTraceAllocator;
use fft::GoodAllocator;
use riscv_transpiler::jit::{JitRunnerRam, MemoryHolder, TraceChunk};
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::fmt::{self, Debug, Formatter};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::sync::{Arc, Mutex, MutexGuard};

/// Alignment of a block's backing allocation, and therefore the strictest
/// alignment a request can be served at: a stricter one is rejected rather
/// than served from an address that does not satisfy it.
const BLOCK_ALIGNMENT: usize = 4096;

struct BlockState {
    /// Bump cursor: alignment padding moves it too, so waste is charged
    /// against the block like any other byte.
    offset: usize,
    live: usize,
}

struct Block {
    base: NonNull<u8>,
    layout: Layout,
    capacity: usize,
    state: Mutex<BlockState>,
}

// SAFETY: `base` is an owned heap allocation that outlives every allocation cut
// from it (each one holds an allocator clone, which holds this `Arc`), and the
// cursor that decides which bytes are handed out is behind the mutex, so no two
// threads can be given overlapping ranges.
unsafe impl Send for Block {}
unsafe impl Sync for Block {}

impl Block {
    fn state(&self) -> MutexGuard<'_, BlockState> {
        self.state
            .lock()
            .expect("trace block state mutex is never poisoned")
    }
}

impl Drop for Block {
    fn drop(&mut self) {
        debug_assert_eq!(
            self.state().live,
            0,
            "trace block dropped while allocations from it are still live"
        );
        // SAFETY: `base`/`layout` are exactly what `Global::allocate` returned
        // in `CpuTraceAllocator::new`, and this is the only deallocation.
        unsafe { Global.deallocate(self.base, self.layout) }
    }
}

/// One finite host trace block, shared by clones.
///
/// Every clone allocates from the same fixed-size block, and the block becomes
/// reusable as a whole only once the last allocation cut from it is freed.
#[derive(Clone)]
pub struct CpuTraceAllocator {
    block: Arc<Block>,
}

impl CpuTraceAllocator {
    pub fn new(bytes: usize) -> Self {
        assert!(bytes > 0, "a trace block must have nonzero capacity");
        let layout = Layout::from_size_align(bytes, BLOCK_ALIGNMENT)
            .expect("host trace block layout is legal");
        let base = Global
            .allocate(layout)
            .expect("host trace block allocation")
            .cast::<u8>();
        Self {
            block: Arc::new(Block {
                base,
                layout,
                capacity: bytes,
                state: Mutex::new(BlockState { offset: 0, live: 0 }),
            }),
        }
    }
}

unsafe impl Allocator for CpuTraceAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout.align() > BLOCK_ALIGNMENT {
            return Err(AllocError);
        }
        let mut state = self.block.state();
        let start = state
            .offset
            .checked_next_multiple_of(layout.align())
            .ok_or(AllocError)?;
        let end = start.checked_add(layout.size()).ok_or(AllocError)?;
        if end > self.block.capacity {
            return Err(AllocError);
        }
        state.offset = end;
        state.live += 1;
        // SAFETY: `end <= capacity` and the block's base is `BLOCK_ALIGNMENT`
        // aligned with `layout.align() <= BLOCK_ALIGNMENT`, so the returned
        // range lies inside the backing allocation and is aligned; the cursor
        // has already moved past it, so no other caller can be given it.
        let ptr = unsafe { NonNull::new_unchecked(self.block.base.as_ptr().add(start)) };
        Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        let mut state = self.block.state();
        state.live = state
            .live
            .checked_sub(1)
            .expect("trace block deallocation without a matching allocation");
        if state.live == 0 {
            state.offset = 0;
        }
    }
}

impl Debug for CpuTraceAllocator {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("CpuTraceAllocator")
            .field("capacity", &self.block.capacity)
            .finish()
    }
}

impl Default for CpuTraceAllocator {
    fn default() -> Self {
        panic!(
            "CpuTraceAllocator has no meaningful default capacity; \
             construct it explicitly via CpuTraceAllocator::new"
        )
    }
}

impl GoodAllocator for CpuTraceAllocator {}

impl HostTraceAllocator for CpuTraceAllocator {
    fn capacity(&self) -> usize {
        self.block.capacity
    }
}

/// Guest RAM for one simulation; `MemoryHolder::allocate_zeroed` owns the
/// layout, including its 2 MiB alignment.
pub struct BoxedMemoryHolder(Box<MemoryHolder>);

impl BoxedMemoryHolder {
    pub(crate) fn new(ram_config: JitRunnerRam) -> Self {
        Self(MemoryHolder::allocate_zeroed(ram_config, Global))
    }
}

impl Deref for BoxedMemoryHolder {
    type Target = MemoryHolder;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BoxedMemoryHolder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// One JIT trace chunk on the ordinary heap.
pub struct BoxedTraceChunk(Box<TraceChunk>);

impl Default for BoxedTraceChunk {
    fn default() -> Self {
        // SAFETY: `TraceChunk` is plain data whose all-zero bit pattern is the
        // state `TraceChunk::empty` produces. `new_zeroed` writes into the heap
        // allocation directly; the chunk is megabytes wide, so building it as a
        // value and moving it would blow the stack.
        Self(unsafe { Box::<TraceChunk>::new_zeroed().assume_init() })
    }
}

impl Deref for BoxedTraceChunk {
    type Target = TraceChunk;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BoxedTraceChunk {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const BLOCK_BYTES: usize = 1 << 12;

    fn layout(size: usize, align: usize) -> Layout {
        Layout::from_size_align(size, align).unwrap()
    }

    #[test]
    fn block_is_finite_and_reusable() {
        let allocator = CpuTraceAllocator::new(BLOCK_BYTES);
        let first = allocator.allocate(layout(BLOCK_BYTES, 1)).unwrap();
        assert!(allocator.allocate(layout(1, 1)).is_err());
        // SAFETY: returning the only allocation cut from this block.
        unsafe { allocator.deallocate(first.cast::<u8>(), layout(BLOCK_BYTES, 1)) };
        let second = allocator.allocate(layout(BLOCK_BYTES, 1)).unwrap();
        assert_eq!(second.cast::<u8>(), first.cast::<u8>());
        unsafe { allocator.deallocate(second.cast::<u8>(), layout(BLOCK_BYTES, 1)) };
    }

    #[test]
    fn block_is_reused_only_after_the_last_reader_releases_it() {
        let allocator = CpuTraceAllocator::new(BLOCK_BYTES);
        let half = BLOCK_BYTES / 2;
        let first = allocator.allocate(layout(half, 1)).unwrap();
        let second = allocator.allocate(layout(half, 1)).unwrap();
        // SAFETY: both allocations came from this block and are returned once.
        unsafe { allocator.deallocate(first.cast::<u8>(), layout(half, 1)) };
        assert!(
            allocator.allocate(layout(1, 1)).is_err(),
            "a partially released block must not be recycled"
        );
        unsafe { allocator.deallocate(second.cast::<u8>(), layout(half, 1)) };
        let reused = allocator.allocate(layout(BLOCK_BYTES, 1)).unwrap();
        unsafe { allocator.deallocate(reused.cast::<u8>(), layout(BLOCK_BYTES, 1)) };
    }

    #[test]
    fn alignment_padding_is_charged_to_the_block() {
        let allocator = CpuTraceAllocator::new(256);
        let head = allocator.allocate(layout(1, 1)).unwrap();
        // 128-aligned, so it starts at 128 and the 127 padding bytes are gone.
        let aligned = allocator.allocate(layout(128, 128)).unwrap();
        assert_eq!(aligned.cast::<u8>().addr().get() % 128, 0);
        assert!(allocator.allocate(layout(1, 1)).is_err());
        // SAFETY: both allocations came from this block and are returned once.
        unsafe {
            allocator.deallocate(head.cast::<u8>(), layout(1, 1));
            allocator.deallocate(aligned.cast::<u8>(), layout(128, 128));
        }
    }

    #[test]
    fn alignment_beyond_the_block_is_rejected() {
        let allocator = CpuTraceAllocator::new(BLOCK_ALIGNMENT * 4);
        assert!(allocator.allocate(layout(8, BLOCK_ALIGNMENT * 2)).is_err());
    }

    #[test]
    fn containers_return_their_credit() {
        let allocator = CpuTraceAllocator::new(BLOCK_BYTES);
        let words = BLOCK_BYTES / size_of::<u32>();
        {
            let mut rows: Vec<u32, CpuTraceAllocator> =
                Vec::with_capacity_in(words, allocator.clone());
            rows.extend(0..words as u32);
            // Probed through the allocator: a container that cannot allocate
            // aborts instead of reporting the exhaustion this asserts.
            assert!(allocator.allocate(layout(1, 1)).is_err());
        }
        let mut reused: Vec<u32, CpuTraceAllocator> = Vec::with_capacity_in(words, allocator);
        reused.push(0);
    }

    #[test]
    fn snapshot_starts_empty() {
        let snapshot = BoxedTraceChunk::default();
        assert_eq!(snapshot.len, 0);
    }
}
