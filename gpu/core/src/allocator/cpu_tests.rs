use super::*;

struct TestBackend(Vec<u8>);

impl StaticAllocationBackend for TestBackend {
    fn as_non_null(&mut self) -> NonNull<u8> {
        NonNull::new(self.0.as_mut_ptr()).unwrap()
    }
    fn len(&self) -> usize {
        self.0.len()
    }
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

// big log_chunk_size = 10 (1024 bytes), small = 4 (16 bytes)
const BIG_LCS: u32 = 10;
const SMALL_LCS: u32 = 4;
const BIG_CHUNK: usize = 1 << BIG_LCS; // 1024
const SMALL_CHUNK: usize = 1 << SMALL_LCS; // 16

fn make_allocator(num_big_chunks: usize) -> InnerStaticAllocator<TestBackend> {
    let total = num_big_chunks * BIG_CHUNK;
    let backend = TestBackend(vec![0u8; total]);
    InnerStaticAllocator::new([backend], BIG_LCS)
}

#[test]
fn carved_pool_allocates_inside_the_carve_at_its_own_granularity() {
    let backend = TestBackend(vec![0u8; 4 * BIG_CHUNK]);
    let parent =
        StaticAllocator::<_, NonConcurrentInnerStaticAllocatorWrapper<_>>::new([backend], BIG_LCS);
    let pool = parent
        .carve(BIG_CHUNK, AllocationPlacement::Bottom, SMALL_LCS)
        .unwrap();
    let addr = |ptr: NonNull<u64>| ptr.as_ptr() as usize;
    let bottom = pool.alloc::<u64>(1, AllocationPlacement::Bottom).unwrap();
    let top = pool.alloc::<u64>(1, AllocationPlacement::Top).unwrap();
    let after_carve = parent.alloc::<u64>(1, AllocationPlacement::Bottom).unwrap();
    assert_eq!(bottom.allocated_bytes(), SMALL_CHUNK);
    assert_eq!(
        addr(top.data.ptr),
        addr(bottom.data.ptr) + BIG_CHUNK - SMALL_CHUNK
    );
    assert_eq!(
        addr(after_carve.data.ptr),
        addr(bottom.data.ptr) + BIG_CHUNK
    );
}

#[test]
fn static_allocation_shrink_preserves_ownership() {
    let backend = TestBackend(vec![0u8; 4 * BIG_CHUNK]);
    let allocator =
        StaticAllocator::<_, NonConcurrentInnerStaticAllocatorWrapper<_>>::new([backend], BIG_LCS);
    let mut allocation = allocator
        .alloc::<u64>(33, AllocationPlacement::BestFit)
        .unwrap();
    let ptr = allocation.data.ptr;
    let alloc_len = allocation.data.alloc_len;

    allocation.shrink_len_to(7);
    assert_eq!(allocation.data.len, 7);
    assert_eq!(allocation.data.alloc_len, alloc_len);
    drop(allocation);

    let reused = allocator
        .alloc::<u64>(33, AllocationPlacement::BestFit)
        .unwrap();
    assert_eq!(reused.data.ptr, ptr);
}

#[test]
fn alloc_alignment_exceeding_chunk_rounds_to_alignment() {
    // When the requested alignment exceeds the chunk granularity, `alloc_len`
    // rounds up to the *alignment*, not the chunk size — this exercises the
    // `.max(alignment)` term in `alloc_impl` (BIG_CHUNK = 1024).
    // Use a 2048-byte alignment (2^11 > BIG_CHUNK). The backend is sized well
    // above alignment + alloc_len so a 2048-aligned block always fits regardless
    // of the (arbitrary) backend base address.
    const EXTRA_ALIGNMENT_LOG2: u32 = 11;
    let extra_alignment = 1usize << EXTRA_ALIGNMENT_LOG2; // 2048 > BIG_CHUNK
    let mut alloc = make_allocator(16);
    let data = alloc
        .alloc_with_extra_alignment::<u64, EXTRA_ALIGNMENT_LOG2>(1, AllocationPlacement::BestFit)
        .unwrap();
    assert_eq!(data.alloc_len, extra_alignment);
    assert_eq!(data.ptr.as_ptr() as usize % extra_alignment, 0);
    alloc.free(data);
}

#[test]
fn zero_length_alloc_takes_no_space() {
    let mut alloc = make_allocator(4);
    let data = alloc.alloc::<u64>(0, AllocationPlacement::BestFit).unwrap();
    assert_eq!(data.alloc_len, 0);
    assert_eq!(alloc.used_mem_current(), 0);
    alloc.free(data);
}
