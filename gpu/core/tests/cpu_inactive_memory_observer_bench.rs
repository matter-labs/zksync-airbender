gpu_core::force_serial_libtest!();

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::allocator::{
    NonConcurrentInnerStaticAllocatorWrapper, StaticAllocationBackend, StaticAllocator,
};
use std::hint::black_box;
use std::ptr::NonNull;
use std::time::Instant;

const BIG_LOG_CHUNK_SIZE: u32 = 10;
const SMALL_LOG_CHUNK_SIZE: u32 = 4;
const BIG_CHUNK: usize = 1 << BIG_LOG_CHUNK_SIZE;
const ITERATIONS: usize = 10_000_000;

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

#[test]
#[ignore = "manual release-mode allocator control-path measurement"]
fn cpu_inactive_memory_observer_alloc_free_throughput() {
    let backend = TestBackend(vec![0; 4 * BIG_CHUNK]);
    let allocator = TestAllocator::new_with_small_allocator(
        [backend],
        BIG_LOG_CHUNK_SIZE,
        SMALL_LOG_CHUNK_SIZE,
        BIG_CHUNK,
    );
    assert_eq!(allocator.get_used_mem_current(), 0);
    assert_eq!(allocator.get_used_mem_peak(), BIG_CHUNK);

    let started = Instant::now();
    for _ in 0..ITERATIONS {
        let allocation = allocator
            .alloc::<u64>(1, AllocationPlacement::BestFit)
            .unwrap();
        black_box(&allocation);
        drop(allocation);
    }
    let elapsed_ns = started.elapsed().as_nanos();

    assert_eq!(allocator.get_used_mem_current(), 0);
    assert_eq!(allocator.get_used_mem_peak(), BIG_CHUNK);
    eprintln!(
        "inactive_memory_observer_alloc_free iterations={ITERATIONS} elapsed_ns={elapsed_ns}"
    );
}
