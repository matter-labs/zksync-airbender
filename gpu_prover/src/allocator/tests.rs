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

const BIG_LCS: u32 = 10;
const SMALL_LCS: u32 = 4;
const BIG_CHUNK: usize = 1 << BIG_LCS;
const SMALL_CHUNK: usize = 1 << SMALL_LCS;

fn make_allocator(
    num_big_chunks: usize,
    small_pool_chunks: usize,
) -> StaticAllocator<TestBackend, NonConcurrentInnerStaticAllocatorWrapper<TestBackend>> {
    let backend = TestBackend(vec![0; num_big_chunks * BIG_CHUNK]);
    StaticAllocator::new_with_small_allocator(
        [backend],
        BIG_LCS,
        SMALL_LCS,
        small_pool_chunks * BIG_CHUNK,
    )
}

#[test]
fn small_and_root_allocations_return_to_empty_baseline() {
    let allocator = make_allocator(4, 1);
    let small_allocator = allocator.small_allocator().unwrap();
    assert_eq!(allocator.get_used_mem_current(), BIG_CHUNK);
    assert_eq!(small_allocator.get_used_mem_current(), 0);

    let small = allocator
        .alloc::<u64>(1, AllocationPlacement::Bottom)
        .unwrap();
    let root = allocator
        .alloc::<u8>(BIG_CHUNK, AllocationPlacement::Top)
        .unwrap();
    assert_eq!(small.data.alloc_len, SMALL_CHUNK);
    assert_eq!(root.data.alloc_len, BIG_CHUNK);

    drop(root);
    drop(small);
    assert_eq!(allocator.get_used_mem_current(), BIG_CHUNK);
    assert_eq!(small_allocator.get_used_mem_current(), 0);
}

#[test]
#[should_panic(expected = "small allocation pool exhausted")]
fn small_pool_exhaustion_never_spills_to_root() {
    let allocator = make_allocator(4, 1);
    let _live = (0..BIG_CHUNK / SMALL_CHUNK)
        .map(|_| {
            allocator
                .alloc::<u64>(1, AllocationPlacement::BestFit)
                .unwrap()
        })
        .collect::<Vec<_>>();
    let _ = allocator.alloc::<u64>(1, AllocationPlacement::BestFit);
}
