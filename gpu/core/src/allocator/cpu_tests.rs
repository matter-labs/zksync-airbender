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

type TestAllocator =
    StaticAllocator<TestBackend, NonConcurrentInnerStaticAllocatorWrapper<TestBackend>>;

// big log_chunk_size = 10 (1024 bytes), small = 4 (16 bytes)
const BIG_LCS: u32 = 10;
const SMALL_LCS: u32 = 4;
const BIG_CHUNK: usize = 1 << BIG_LCS; // 1024
const SMALL_CHUNK: usize = 1 << SMALL_LCS; // 16

fn make_parent(num_big_chunks: usize) -> TestAllocator {
    let backend = TestBackend(vec![0u8; num_big_chunks * BIG_CHUNK]);
    StaticAllocator::new([backend], BIG_LCS)
}

fn make_pools(num_big_chunks: usize, small_pool_chunks: usize) -> (TestAllocator, TestAllocator) {
    let parent = make_parent(num_big_chunks);
    let small = parent
        .carve(
            small_pool_chunks * BIG_CHUNK,
            AllocationPlacement::Bottom,
            SMALL_LCS,
        )
        .unwrap();
    (parent, small)
}

fn make_allocator_no_small(num_big_chunks: usize) -> InnerStaticAllocator<TestBackend> {
    let total = num_big_chunks * BIG_CHUNK;
    let backend = TestBackend(vec![0u8; total]);
    InnerStaticAllocator::new([backend], BIG_LCS)
}

fn addr<T>(
    allocation: &StaticAllocation<
        T,
        TestBackend,
        NonConcurrentInnerStaticAllocatorWrapper<TestBackend>,
    >,
) -> usize {
    allocation.data.ptr.as_ptr() as usize
}

#[test]
fn small_allocation_threshold_is_a_quarter_big_chunk() {
    assert!(!is_small_allocation(0, BIG_LCS));
    assert!(is_small_allocation(1, BIG_LCS));
    assert!(is_small_allocation(BIG_CHUNK / 4, BIG_LCS));
    assert!(!is_small_allocation(BIG_CHUNK / 4 + 1, BIG_LCS));
}

#[test]
fn carved_pool_rounds_to_its_own_chunk() {
    let (parent, small) = make_pools(4, 1);
    let small_data = small.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let big_data = parent
        .alloc::<u64>(1, AllocationPlacement::BestFit)
        .unwrap();
    assert_eq!(small_data.allocated_bytes(), SMALL_CHUNK);
    assert_eq!(big_data.allocated_bytes(), BIG_CHUNK);
}

#[test]
fn carved_pool_reuses_freed_space() {
    let (_parent, small) = make_pools(4, 1);
    let first = small.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let first_addr = addr(&first);
    drop(first);
    let second = small.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    assert_eq!(addr(&second), first_addr);
}

#[test]
fn carved_pool_allocations_stay_inside_the_carve() {
    let (parent, small) = make_pools(4, 1);
    let bottom = small.alloc::<u64>(1, AllocationPlacement::Bottom).unwrap();
    let top = small.alloc::<u64>(1, AllocationPlacement::Top).unwrap();
    let best = small.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let pool_start = addr(&bottom);
    assert_eq!(addr(&top), pool_start + BIG_CHUNK - SMALL_CHUNK);
    assert_eq!(addr(&best), pool_start + SMALL_CHUNK);
    let after_carve = parent.alloc::<u8>(1, AllocationPlacement::Bottom).unwrap();
    assert_eq!(addr(&after_carve), pool_start + BIG_CHUNK);
}

#[test]
fn carved_pool_oom_leaves_parent_usable() {
    // 1 big chunk = 1024 bytes for the small pool, 16-byte chunks → 64 slots
    let (parent, small) = make_pools(4, 1);
    let allocations = (0..64)
        .map(|_| small.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap())
        .collect::<Vec<_>>();
    assert!(small.alloc::<u64>(1, AllocationPlacement::BestFit).is_err());
    assert!(parent.alloc::<u64>(1, AllocationPlacement::BestFit).is_ok());
    drop(allocations);
}

#[test]
fn carve_returns_to_parent_after_pool_and_allocations_drop() {
    let (parent, small) = make_pools(4, 1);
    let allocation = small.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    assert_eq!(small.get_used_mem_current(), SMALL_CHUNK);
    assert_eq!(parent.get_used_mem_current(), BIG_CHUNK);
    drop(small);
    assert_eq!(parent.get_used_mem_current(), BIG_CHUNK);
    drop(allocation);
    assert_eq!(parent.get_used_mem_current(), 0);
}

#[test]
fn bounded_allocation_respects_bounds() {
    let parent = make_parent(8);
    let base = addr(&parent.alloc::<u8>(1, AllocationPlacement::Bottom).unwrap());
    let bounds = base + 2 * BIG_CHUNK..base + 5 * BIG_CHUNK;
    let bottom = parent
        .alloc_in::<u64>(1, AllocationPlacement::Bottom, bounds.clone())
        .unwrap();
    let top = parent
        .alloc_in::<u64>(1, AllocationPlacement::Top, bounds.clone())
        .unwrap();
    assert_eq!(addr(&bottom), bounds.start);
    assert_eq!(addr(&top), bounds.end - BIG_CHUNK);
    assert!(parent
        .alloc_in::<u8>(2 * BIG_CHUNK, AllocationPlacement::BestFit, bounds)
        .is_err());
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
    let mut alloc = make_allocator_no_small(16);
    let data = alloc
        .alloc_with_extra_alignment::<u64, EXTRA_ALIGNMENT_LOG2>(1, AllocationPlacement::BestFit)
        .unwrap();
    assert_eq!(data.alloc_len, extra_alignment);
    assert_eq!(data.ptr.as_ptr() as usize % extra_alignment, 0);
    alloc.free(data);
}

#[test]
fn zero_length_alloc_takes_no_space() {
    let mut alloc = make_allocator_no_small(4);
    let data = alloc.alloc::<u64>(0, AllocationPlacement::BestFit).unwrap();
    assert_eq!(data.alloc_len, 0);
    assert_eq!(alloc.used_mem_current(), 0);
    alloc.free(data);
}

#[test]
#[should_panic(expected = "carved pool must be a positive multiple of its chunk size")]
fn carved_pool_chunk_must_divide_the_carve() {
    let parent = make_parent(4);
    let _ = parent.carve(BIG_CHUNK, AllocationPlacement::Bottom, BIG_LCS + 1);
}
