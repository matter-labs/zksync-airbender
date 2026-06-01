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

fn make_allocator(
    num_big_chunks: usize,
    small_pool_chunks: usize,
) -> InnerStaticAllocator<TestBackend> {
    let total = num_big_chunks * BIG_CHUNK;
    let backend = TestBackend(vec![0u8; total]);
    let pool_size = small_pool_chunks * BIG_CHUNK;
    InnerStaticAllocator::new_with_small_allocator([backend], BIG_LCS, SMALL_LCS, pool_size)
}

fn make_allocator_no_small(num_big_chunks: usize) -> InnerStaticAllocator<TestBackend> {
    let total = num_big_chunks * BIG_CHUNK;
    let backend = TestBackend(vec![0u8; total]);
    InnerStaticAllocator::new([backend], BIG_LCS)
}

#[test]
fn small_alloc_basic_roundtrip() {
    let mut alloc = make_allocator(4, 1);
    // Allocate 1 u64 = 8 bytes, below threshold (256), should go to small allocator
    let data = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    assert_eq!(data.len, 1);
    // alloc_len should be rounded to small chunk size (16), not big (1024)
    assert_eq!(data.alloc_len, SMALL_CHUNK);
    alloc.free(data);
}

#[test]
fn small_alloc_reuse_after_free() {
    let mut alloc = make_allocator(4, 1);
    let data1 = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let ptr1 = data1.ptr;
    alloc.free(data1);
    let data2 = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let ptr2 = data2.ptr;
    // Should reuse the same address after free
    assert_eq!(ptr1, ptr2);
    alloc.free(data2);
}

#[test]
fn big_alloc_bypasses_small() {
    let mut alloc = make_allocator(4, 1);
    // Allocate above threshold: 33 u64s = 264 bytes > 256 threshold
    let data = alloc
        .alloc::<u64>(33, AllocationPlacement::BestFit)
        .unwrap();
    // alloc_len should be rounded to big chunk size (1024)
    assert_eq!(data.alloc_len, BIG_CHUNK);
    alloc.free(data);
}

#[test]
fn free_routes_correctly_mixed() {
    let mut alloc = make_allocator(4, 1);
    // Small allocation
    let small = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    // Big allocation
    let big = alloc
        .alloc::<u64>(33, AllocationPlacement::BestFit)
        .unwrap();
    // Free in reverse order — should not panic
    alloc.free(big);
    alloc.free(small);
}

#[test]
fn usage_counters_correct() {
    let mut alloc = make_allocator(4, 1);
    // 1 big chunk is reserved for small pool, so big tracker has 4 chunks used (pool=1)
    // Initial: big_used = 1 chunk (pool), small_used = 0
    // get_used_mem_current = big_used - backing_len + small_used = 1024 - 1024 + 0 = 0
    assert_eq!(
        alloc.tracker.get_used_mem_current() - BIG_CHUNK
            + alloc.small.as_ref().unwrap().tracker.get_used_mem_current(),
        0
    );

    // Allocate a small item (8 bytes → 16 bytes rounded)
    let small = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let big_used = alloc.tracker.get_used_mem_current();
    let small_used = alloc.small.as_ref().unwrap().tracker.get_used_mem_current();
    // big_used still = 1024 (the pool chunk), small_used = 16
    assert_eq!(big_used, BIG_CHUNK);
    assert_eq!(small_used, SMALL_CHUNK);
    // Effective = 1024 - 1024 + 16 = 16
    assert_eq!(big_used - BIG_CHUNK + small_used, SMALL_CHUNK);

    alloc.free(small);
}

#[test]
fn threshold_boundary() {
    let mut alloc = make_allocator(4, 1);
    // Exactly at threshold: 32 u64s = 256 bytes = threshold → small
    let at = alloc
        .alloc::<u64>(32, AllocationPlacement::BestFit)
        .unwrap();
    assert!(at.alloc_len < BIG_CHUNK); // went to small allocator
    alloc.free(at);

    // One byte over: 33 u64s = 264 bytes > threshold → big
    let over = alloc
        .alloc::<u64>(33, AllocationPlacement::BestFit)
        .unwrap();
    assert_eq!(over.alloc_len, BIG_CHUNK); // went to big allocator
    alloc.free(over);
}

#[test]
fn small_pool_oom() {
    // 1 big chunk = 1024 bytes for small pool, small chunk = 16 bytes → 64 small slots
    let mut alloc = make_allocator(4, 1);
    let mut allocs = Vec::new();
    // Fill the pool
    for _ in 0..64 {
        allocs.push(alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap());
    }
    // Next small alloc should fail
    let result = alloc.alloc::<u64>(1, AllocationPlacement::BestFit);
    assert!(result.is_err());
    // Free all
    for a in allocs {
        alloc.free(a);
    }
}

#[test]
fn disabled_small_allocator_identical_behavior() {
    let mut alloc = make_allocator_no_small(4);
    assert!(alloc.small.is_none());
    // Small allocation goes to big tracker, rounded to 1024
    let data = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    assert_eq!(data.alloc_len, BIG_CHUNK);
    alloc.free(data);
}

#[test]
fn zero_length_alloc_goes_to_big() {
    let mut alloc = make_allocator(4, 1);
    // Zero-length allocs bypass the small allocator (byte_len == 0)
    let data = alloc.alloc::<u64>(0, AllocationPlacement::BestFit).unwrap();
    assert_eq!(data.alloc_len, 0);
    alloc.free(data);
}

#[test]
fn many_small_allocs_different_placements() {
    let mut alloc = make_allocator(4, 1);
    let bottom = alloc.alloc::<u64>(1, AllocationPlacement::Bottom).unwrap();
    let top = alloc.alloc::<u64>(1, AllocationPlacement::Top).unwrap();
    let best = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    // All should be in small allocator range, with distinct addresses
    let small = alloc.small.as_ref().unwrap();
    assert!(small.owns(bottom.ptr.as_ptr() as usize));
    assert!(small.owns(top.ptr.as_ptr() as usize));
    assert!(small.owns(best.ptr.as_ptr() as usize));
    assert_ne!(bottom.ptr, top.ptr);
    assert_ne!(bottom.ptr, best.ptr);
    alloc.free(bottom);
    alloc.free(top);
    alloc.free(best);
}

#[test]
#[should_panic(expected = "small chunk size must be smaller than big chunk size")]
fn small_chunk_size_must_be_smaller() {
    let backend = TestBackend(vec![0u8; 4 * BIG_CHUNK]);
    InnerStaticAllocator::new_with_small_allocator([backend], BIG_LCS, BIG_LCS, BIG_CHUNK);
}

#[test]
#[should_panic(expected = "small pool size must be a positive multiple of the big chunk size")]
fn pool_size_must_be_multiple() {
    let backend = TestBackend(vec![0u8; 4 * BIG_CHUNK]);
    InnerStaticAllocator::new_with_small_allocator([backend], BIG_LCS, SMALL_LCS, BIG_CHUNK + 1);
}
