use fft::GoodAllocator;
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Allocator for one reusable trace block of fixed capacity.
pub trait HostTraceAllocator: GoodAllocator {
    fn capacity(&self) -> usize;
}

const BLOCK_ALIGNMENT: usize = 4096;

#[derive(Debug)]
struct Block {
    region: NonNull<u8>,
    layout: Layout,
    handed_out: AtomicBool,
}

// SAFETY: the region is an owned heap allocation handed to at most one
// container at a time; clones only share its owner.
unsafe impl Send for Block {}
unsafe impl Sync for Block {}

impl Drop for Block {
    fn drop(&mut self) {
        // SAFETY: `region`/`layout` are what `Global::allocate` returned in
        // `CpuTraceAllocator::new`, and this is the only deallocation.
        unsafe { Global.deallocate(self.region, self.layout) }
    }
}

/// One preallocated trace block. The producers cut exactly one container from
/// a block, so the block is a single credit: taken with the container,
/// returned when the container drops.
#[derive(Clone, Debug)]
pub struct CpuTraceAllocator(Arc<Block>);

impl CpuTraceAllocator {
    pub fn new(bytes: usize) -> Self {
        let layout = Layout::from_size_align(bytes, BLOCK_ALIGNMENT)
            .expect("host trace block layout is legal");
        let region = Global
            .allocate(layout)
            .expect("host trace block allocation")
            .cast::<u8>();
        Self(Arc::new(Block {
            region,
            layout,
            handed_out: AtomicBool::new(false),
        }))
    }
}

unsafe impl Allocator for CpuTraceAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let block = &*self.0;
        assert!(
            layout.size() <= block.layout.size() && layout.align() <= BLOCK_ALIGNMENT,
            "{layout:?} does not fit a trace block of {:?}",
            block.layout
        );
        assert!(
            !block.handed_out.swap(true, Ordering::SeqCst),
            "trace block is already handed out"
        );
        Ok(NonNull::slice_from_raw_parts(block.region, layout.size()))
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
        assert_eq!(ptr, self.0.region);
        assert!(self.0.handed_out.swap(false, Ordering::SeqCst));
    }
}

impl Default for CpuTraceAllocator {
    fn default() -> Self {
        panic!("a trace block has no default capacity; use CpuTraceAllocator::new")
    }
}

impl GoodAllocator for CpuTraceAllocator {}

impl HostTraceAllocator for CpuTraceAllocator {
    fn capacity(&self) -> usize {
        self.0.layout.size()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const BLOCK_BYTES: usize = 1 << 12;

    #[test]
    fn a_released_block_is_handed_out_again() {
        let allocator = CpuTraceAllocator::new(BLOCK_BYTES);
        let layout = Layout::from_size_align(BLOCK_BYTES, 8).unwrap();
        let first = allocator.allocate(layout).unwrap().cast::<u8>();
        // SAFETY: returning the only allocation cut from this block.
        unsafe { allocator.deallocate(first, layout) };
        let second = allocator.allocate(layout).unwrap().cast::<u8>();
        assert_eq!(first, second);
        unsafe { allocator.deallocate(second, layout) };
    }

    #[test]
    #[should_panic(expected = "already handed out")]
    fn a_block_serves_one_container_at_a_time() {
        let allocator = CpuTraceAllocator::new(BLOCK_BYTES);
        let layout = Layout::from_size_align(8, 8).unwrap();
        let _first = allocator.allocate(layout).unwrap();
        let _ = allocator.allocate(layout);
    }
}
