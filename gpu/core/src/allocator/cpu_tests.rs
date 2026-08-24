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

type TestStaticAllocator =
    StaticAllocator<TestBackend, NonConcurrentInnerStaticAllocatorWrapper<TestBackend>>;

fn make_static_allocator(num_big_chunks: usize, small_pool_chunks: usize) -> TestStaticAllocator {
    let total = num_big_chunks * BIG_CHUNK;
    let backend = TestBackend(vec![0u8; total]);
    let pool_size = small_pool_chunks * BIG_CHUNK;
    TestStaticAllocator::new_with_small_allocator([backend], BIG_LCS, SMALL_LCS, pool_size)
}

fn make_static_allocator_no_small(num_big_chunks: usize) -> TestStaticAllocator {
    let total = num_big_chunks * BIG_CHUNK;
    let backend = TestBackend(vec![0u8; total]);
    TestStaticAllocator::new([backend], BIG_LCS)
}

#[test]
fn cpu_memory_observer_distinguishes_small_pool_logical_peak() {
    let alloc = make_static_allocator(4, 1);

    // The inactive observer slots are host bookkeeping: constructing them
    // neither consumes pool bytes nor changes the outer tracker's peak.
    let inactive_start = alloc.get_memory_usage();
    assert_eq!(inactive_start.physical_backing_bytes, BIG_CHUNK);
    assert_eq!(inactive_start.logical_live_bytes, 0);
    assert_eq!(alloc.get_used_mem_peak(), BIG_CHUNK);
    let inactive_probe = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    drop(inactive_probe);
    assert_eq!(alloc.get_memory_usage(), inactive_start);
    assert_eq!(alloc.get_used_mem_peak(), BIG_CHUNK);

    let observer = alloc.observe_memory_high_water();

    let small = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    drop(small);

    let report = observer.finish();
    assert_eq!(
        report.start,
        PoolMemoryUsage {
            physical_backing_bytes: BIG_CHUNK,
            logical_live_bytes: 0,
        }
    );
    assert_eq!(report.physical_backing_peak_bytes, BIG_CHUNK);
    assert_eq!(report.logical_live_peak_bytes, SMALL_CHUNK);
    assert_eq!(report.summed_requested_bytes, size_of::<u64>());
    assert_eq!(report.peak_window_end, report.start);
    assert_eq!(report.return_to_entry, report.start);
}

#[test]
fn cpu_memory_observer_tracks_mixed_physical_and_logical_peaks() {
    let alloc = make_static_allocator(4, 1);
    let observer = alloc.observe_memory_high_water();

    let small = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let big = alloc
        .alloc::<u64>(33, AllocationPlacement::BestFit)
        .unwrap();
    drop(big);
    drop(small);

    let report = observer.finish();
    assert_eq!(report.start.physical_backing_bytes, BIG_CHUNK);
    assert_eq!(report.start.logical_live_bytes, 0);
    assert_eq!(report.physical_backing_peak_bytes, 2 * BIG_CHUNK);
    assert_eq!(report.logical_live_peak_bytes, BIG_CHUNK + SMALL_CHUNK);
    assert_eq!(report.summed_requested_bytes, (1 + 33) * size_of::<u64>());
    assert_eq!(report.return_to_entry, report.start);
}

#[test]
fn cpu_nested_memory_observers_survive_legacy_peak_reset() {
    let alloc = make_static_allocator(4, 1);
    let whole = alloc.observe_memory_high_water();
    let preexisting = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let mut backward = alloc.observe_memory_high_water();
    let backward_start = alloc.get_memory_usage();

    // Establish a peak strictly above the current usage at the legacy reset
    // after both live observers have started. A mutation that clamps either
    // scoped peak to current would lose this value; the later allocation is
    // deliberately smaller so it cannot restore the peak accidentally.
    let pre_reset_peak = alloc
        .alloc::<u64>(130, AllocationPlacement::BestFit)
        .unwrap();
    drop(pre_reset_peak);
    assert_eq!(alloc.get_memory_usage(), backward_start);

    alloc.reset_used_mem_peak();
    let big = alloc
        .alloc::<u64>(33, AllocationPlacement::BestFit)
        .unwrap();
    drop(big);

    let sealed = backward.seal();
    assert_eq!(sealed.start, backward_start);
    assert_eq!(sealed.physical_backing_peak_bytes, 3 * BIG_CHUNK);
    assert_eq!(sealed.logical_live_peak_bytes, 2 * BIG_CHUNK + SMALL_CHUNK);
    assert_eq!(sealed.summed_requested_bytes, (130 + 33) * size_of::<u64>());
    assert_eq!(sealed.peak_window_end, backward_start);

    let backward_report = backward.finish();
    assert_eq!(backward_report.return_to_entry, backward_start);
    drop(preexisting);
    let whole_report = whole.finish();
    assert_eq!(whole_report.start.physical_backing_bytes, BIG_CHUNK);
    assert_eq!(whole_report.start.logical_live_bytes, 0);
    assert_eq!(whole_report.physical_backing_peak_bytes, 3 * BIG_CHUNK);
    assert_eq!(
        whole_report.logical_live_peak_bytes,
        2 * BIG_CHUNK + SMALL_CHUNK
    );
    assert_eq!(
        whole_report.summed_requested_bytes,
        (130 + 1 + 33) * size_of::<u64>()
    );
    assert_eq!(whole_report.return_to_entry, whole_report.start);
}

#[test]
fn cpu_memory_observer_drop_cancels_slot() {
    let alloc = make_static_allocator_no_small(4);
    drop(alloc.observe_memory_high_water());

    let first = alloc.observe_memory_high_water();
    let second = alloc.observe_memory_high_water();
    let third = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        alloc.observe_memory_high_water()
    }));
    assert!(third.is_err());
    drop(first);
    drop(second);

    // Both slots must be reusable after unfinished observers are dropped.
    let first = alloc.observe_memory_high_water();
    let second = alloc.observe_memory_high_water();
    drop(first);
    drop(second);
}

#[test]
fn cpu_memory_observer_without_small_pool_has_equal_metrics() {
    let alloc = make_static_allocator_no_small(4);
    let observer = alloc.observe_memory_high_water();

    let allocation = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    alloc.reset_used_mem_peak();
    drop(allocation);

    let report = observer.finish();
    assert_eq!(report.start.physical_backing_bytes, 0);
    assert_eq!(report.start.logical_live_bytes, 0);
    assert_eq!(report.physical_backing_peak_bytes, BIG_CHUNK);
    assert_eq!(report.logical_live_peak_bytes, BIG_CHUNK);
    assert_eq!(report.peak_window_end.physical_backing_bytes, 0);
    assert_eq!(report.peak_window_end.logical_live_bytes, 0);
    assert_eq!(report.return_to_entry, report.start);
}

#[test]
fn cpu_memory_observer_seal_freezes_backward_window() {
    let alloc = make_static_allocator(8, 1);
    let whole = alloc.observe_memory_high_water();
    let mut backward = alloc.observe_memory_high_water();

    let backward_allocation = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let sealed = backward.seal();

    let later_allocation = alloc
        .alloc::<u64>(130, AllocationPlacement::BestFit)
        .unwrap();
    drop(later_allocation);
    drop(backward_allocation);

    let backward_report = backward.finish();
    let whole_report = whole.finish();
    assert_eq!(backward_report.physical_backing_peak_bytes, BIG_CHUNK);
    assert_eq!(backward_report.logical_live_peak_bytes, SMALL_CHUNK);
    assert_eq!(backward_report.summed_requested_bytes, size_of::<u64>());
    assert_eq!(backward_report.peak_window_end, sealed.peak_window_end);
    assert_eq!(backward_report.return_to_entry, backward_report.start);

    assert_eq!(whole_report.physical_backing_peak_bytes, 3 * BIG_CHUNK);
    assert_eq!(
        whole_report.logical_live_peak_bytes,
        2 * BIG_CHUNK + SMALL_CHUNK
    );
    assert_eq!(
        whole_report.summed_requested_bytes,
        (1 + 130) * size_of::<u64>()
    );
    assert_eq!(whole_report.return_to_entry, whole_report.start);
}

#[test]
fn cpu_memory_observer_requested_bytes_are_unrounded_and_counted_once() {
    let alloc = make_static_allocator(4, 1);
    let observer = alloc.observe_memory_high_water();

    let plain = alloc.alloc::<u8>(1, AllocationPlacement::BestFit).unwrap();
    let aligned = alloc
        .alloc_with_extra_alignment::<u8, 6>(17, AllocationPlacement::BestFit)
        .unwrap();
    assert!(alloc
        .alloc::<u8>(5 * BIG_CHUNK, AllocationPlacement::BestFit)
        .is_err());
    drop(aligned);
    drop(plain);

    let report = observer.finish();
    assert_eq!(report.summed_requested_bytes, 18);
    assert_eq!(report.return_to_entry, report.start);
}

#[test]
fn static_allocation_shrink_len_to_full_pool_round_trips() {
    let alloc = make_static_allocator_no_small(4);
    let baseline = alloc.get_memory_usage();
    let original_len = 33;
    let mut allocation = alloc
        .alloc::<u64>(original_len, AllocationPlacement::BestFit)
        .unwrap();
    let original_ptr = allocation.data.ptr;
    let original_alloc_len = allocation.data.alloc_len;
    assert_eq!(allocation.data.len, original_len);
    assert_eq!(original_alloc_len, BIG_CHUNK);

    allocation.shrink_len_to(7);
    assert_eq!(allocation.data.len, 7);
    assert_eq!(allocation.data.ptr, original_ptr);
    assert_eq!(allocation.data.alloc_len, original_alloc_len);
    drop(allocation);
    assert_eq!(alloc.get_memory_usage(), baseline);

    let reused = alloc
        .alloc::<u64>(original_len, AllocationPlacement::BestFit)
        .unwrap();
    assert_eq!(reused.data.ptr, original_ptr);
    assert_eq!(reused.data.alloc_len, original_alloc_len);
    drop(reused);
    assert_eq!(alloc.get_memory_usage(), baseline);
}

#[test]
fn static_allocation_shrink_len_to_small_pool_round_trips() {
    let alloc = make_static_allocator(4, 1);
    let baseline = alloc.get_memory_usage();
    let original_len = 3;
    let mut allocation = alloc
        .alloc::<u64>(original_len, AllocationPlacement::BestFit)
        .unwrap();
    let original_ptr = allocation.data.ptr;
    let original_alloc_len = allocation.data.alloc_len;
    assert_eq!(allocation.data.len, original_len);
    assert_eq!(original_alloc_len, 2 * SMALL_CHUNK);

    allocation.shrink_len_to(1);
    assert_eq!(allocation.data.len, 1);
    assert_eq!(allocation.data.ptr, original_ptr);
    assert_eq!(allocation.data.alloc_len, original_alloc_len);
    drop(allocation);
    assert_eq!(alloc.get_memory_usage(), baseline);

    let reused = alloc
        .alloc::<u64>(original_len, AllocationPlacement::BestFit)
        .unwrap();
    assert_eq!(reused.data.ptr, original_ptr);
    assert_eq!(reused.data.alloc_len, original_alloc_len);
    drop(reused);
    assert_eq!(alloc.get_memory_usage(), baseline);
}

#[test]
fn static_allocation_shrink_len_to_preserves_accounting_and_units() {
    let alloc = make_static_allocator(4, 1);
    let baseline = alloc.get_memory_usage();
    let mut allocation = alloc.alloc::<u64>(3, AllocationPlacement::BestFit).unwrap();
    let original_ptr = allocation.data.ptr;
    let original_alloc_len = allocation.data.alloc_len;
    assert_eq!(allocation.data.len, 3);
    assert_eq!(original_alloc_len, 2 * SMALL_CHUNK);
    let start = alloc.get_memory_usage();
    assert_eq!(
        start,
        PoolMemoryUsage {
            physical_backing_bytes: BIG_CHUNK,
            logical_live_bytes: 2 * SMALL_CHUNK,
        }
    );
    let mut observer = alloc.observe_memory_high_water();

    allocation.shrink_len_to(1);
    assert_eq!(allocation.data.len, 1);
    assert_eq!(allocation.data.ptr, original_ptr);
    assert_eq!(allocation.data.alloc_len, original_alloc_len);
    let snapshot = observer.seal();
    assert_eq!(snapshot.start, start);
    assert_eq!(
        snapshot.physical_backing_peak_bytes,
        start.physical_backing_bytes
    );
    assert_eq!(snapshot.logical_live_peak_bytes, start.logical_live_bytes);
    assert_eq!(snapshot.summed_requested_bytes, 0);
    assert_eq!(snapshot.peak_window_end, start);

    let report = observer.finish();
    assert_eq!(report.start, start);
    assert_eq!(
        report.physical_backing_peak_bytes,
        start.physical_backing_bytes
    );
    assert_eq!(report.logical_live_peak_bytes, start.logical_live_bytes);
    assert_eq!(report.summed_requested_bytes, 0);
    assert_eq!(report.peak_window_end, start);
    assert_eq!(report.return_to_entry, start);

    drop(allocation);
    assert_eq!(alloc.get_memory_usage(), baseline);
}

#[test]
fn static_allocation_shrink_len_to_same_and_zero() {
    let alloc = make_static_allocator(4, 1);
    let baseline = alloc.get_memory_usage();
    let mut allocation = alloc.alloc::<u16>(9, AllocationPlacement::BestFit).unwrap();
    let original_ptr = allocation.data.ptr;
    let original_alloc_len = allocation.data.alloc_len;

    allocation.shrink_len_to(9);
    assert_eq!(allocation.data.len, 9);
    assert_eq!(allocation.data.ptr, original_ptr);
    assert_eq!(allocation.data.alloc_len, original_alloc_len);
    allocation.shrink_len_to(0);
    assert_eq!(allocation.data.len, 0);
    assert_eq!(allocation.data.ptr, original_ptr);
    assert_eq!(allocation.data.alloc_len, original_alloc_len);

    drop(allocation);
    assert_eq!(alloc.get_memory_usage(), baseline);
}

#[test]
#[should_panic(expected = "StaticAllocation::shrink_len_to cannot grow")]
fn static_allocation_shrink_len_to_rejects_growth() {
    let alloc = make_static_allocator(4, 1);
    let baseline = alloc.get_memory_usage();
    let mut allocation = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
    let original_ptr = allocation.data.ptr;
    let original_alloc_len = allocation.data.alloc_len;
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        allocation.shrink_len_to(2);
    }))
    .expect_err("growth must panic");
    assert_eq!(allocation.data.len, 1);
    assert_eq!(allocation.data.ptr, original_ptr);
    assert_eq!(allocation.data.alloc_len, original_alloc_len);
    drop(allocation);
    assert_eq!(alloc.get_memory_usage(), baseline);
    std::panic::resume_unwind(panic);
}

/// Sweeps `byte_len` across the small/big routing threshold (256 B for
/// `make_allocator(4, 1)`), asserting the exact `alloc_len` rounding on each
/// side. Folds `small_alloc_basic_roundtrip` (below-threshold case),
/// `threshold_boundary` (at-threshold + above-threshold cases), and
/// `big_alloc_bypasses_small` (above-threshold case, same assertion as
/// `threshold_boundary`'s upper half) — all three overlapped on this one
/// byte_len-vs-threshold dimension.
#[test]
fn small_vs_big_alloc_routing_by_threshold() {
    enum Expect {
        /// below threshold (256 B): routed to small allocator, alloc_len
        /// rounded exactly to SMALL_CHUNK (16). [small_alloc_basic_roundtrip]
        SmallExact,
        /// == threshold (256 B): still routed to small allocator, alloc_len
        /// strictly less than BIG_CHUNK. [threshold_boundary, lower half]
        SmallBound,
        /// above threshold (264 B): routed to big allocator, alloc_len
        /// rounded exactly to BIG_CHUNK (1024). [threshold_boundary upper
        /// half + big_alloc_bypasses_small]
        Big,
    }

    let mut alloc = make_allocator(4, 1);
    let cases = [
        (1usize, Expect::SmallExact), // 1 u64 = 8 B
        (32, Expect::SmallBound),     // 32 u64s = 256 B
        (33, Expect::Big),            // 33 u64s = 264 B
    ];

    for (count, expect) in cases {
        let data = alloc
            .alloc::<u64>(count, AllocationPlacement::BestFit)
            .unwrap();
        match expect {
            Expect::SmallExact => {
                assert_eq!(data.len, count);
                assert_eq!(data.alloc_len, SMALL_CHUNK);
            }
            Expect::SmallBound => assert!(data.alloc_len < BIG_CHUNK),
            Expect::Big => assert_eq!(data.alloc_len, BIG_CHUNK),
        }
        alloc.free(data);
    }
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
fn free_routes_correctly_mixed() {
    let mut alloc = make_allocator(4, 1);
    let small = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
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
fn alloc_alignment_exceeding_chunk_rounds_to_alignment() {
    // When the requested alignment exceeds the chunk granularity, the shared
    // allocation tail rounds `alloc_len` up to the *alignment*, not the chunk
    // size — this exercises the `.max(alignment)` term in `alloc_from_tracker`
    // (BIG_CHUNK = 1024; a plain 8-byte alloc rounds to 1024, see the test above).
    // Use a 2048-byte alignment (2^11 > BIG_CHUNK). The backend is sized well
    // above alignment + alloc_len so a 2048-aligned block always fits regardless
    // of the (arbitrary) backend base address.
    const EXTRA_ALIGNMENT_LOG2: u32 = 11;
    let extra_alignment = 1usize << EXTRA_ALIGNMENT_LOG2; // 2048 > BIG_CHUNK
    let mut alloc = make_allocator_no_small(16);
    let data = alloc
        .alloc_with_extra_alignment::<u64, EXTRA_ALIGNMENT_LOG2>(1, AllocationPlacement::BestFit)
        .unwrap();
    // `.max(alignment)` took effect: rounded to the 2048 alignment, not the 1024
    // chunk (which is what the same alloc without extra alignment would give).
    assert_eq!(data.alloc_len, extra_alignment);
    assert_eq!(data.ptr.as_ptr() as usize % extra_alignment, 0);
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
