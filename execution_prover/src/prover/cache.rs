use crate::messages::SimulationResult;
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, TracingDataHost};
use std::collections::VecDeque;

pub(super) struct TraceCacheEntry<A: HostTraceAllocator> {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
}

impl<A: HostTraceAllocator> TraceCacheEntry<A> {
    /// Trace blocks this entry keeps out of the pool.
    pub(super) fn block_count(&self) -> usize {
        self.inits_and_teardowns
            .as_ref()
            .map_or(0, |trace| trace.block_count())
            + self
                .tracing_data
                .as_ref()
                .map_or(0, |trace| trace.block_count())
    }
}

pub(super) struct TraceCache<A: HostTraceAllocator> {
    pub(super) entries: VecDeque<TraceCacheEntry<A>>,
    pub(super) total_requests_count: usize,
    pub(super) trivial_unified_inits_and_teardowns_count: usize,
    pub(super) simulation_result: Option<SimulationResult>,
}

impl<A: HostTraceAllocator> Default for TraceCache<A> {
    fn default() -> Self {
        Self {
            entries: VecDeque::new(),
            total_requests_count: 0,
            trivial_unified_inits_and_teardowns_count: 0,
            simulation_result: None,
        }
    }
}

impl<A: HostTraceAllocator> TraceCache<A> {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn push_back(&mut self, entry: TraceCacheEntry<A>) {
        self.entries.push_back(entry);
    }

    /// Trace blocks the whole cache is holding.
    pub(super) fn block_count(&self) -> usize {
        self.entries.iter().map(TraceCacheEntry::block_count).sum()
    }

    /// Entries to evict, oldest first, until the cache fits `quota` blocks.
    ///
    /// Whole entries only: half an entry is not a cache hit. An entry larger
    /// than the whole quota goes too, so a zero quota drains the cache rather
    /// than pinning its first entry forever.
    pub(super) fn evict_to_fit(&mut self, quota: usize) -> Vec<TraceCacheEntry<A>> {
        let mut evicted = Vec::new();
        let mut held = self.block_count();
        while held > quota {
            let Some(entry) = self.entries.pop_front() else {
                break;
            };
            held -= entry.block_count();
            evicted.push(entry);
        }
        evicted
    }

    pub(super) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(super) fn is_not_initialized(&self) -> bool {
        self.entries.is_empty()
            && self.total_requests_count == 0
            && self.trivial_unified_inits_and_teardowns_count == 0
            && self.simulation_result.is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use execution_prover_model::circuit_type::UnrolledCircuitType;
    use execution_prover_model::trace::{
        ChunkedTraceHolder, TracingDataHost, UnrolledTracingDataHost,
    };
    use std::sync::Arc;

    /// A cache entry owning `blocks` trace blocks. One chunk is one block, as
    /// in `ChunkedTraceHolder::into_allocators`.
    fn entry(
        sequence_id: usize,
        blocks: usize,
    ) -> TraceCacheEntry<crate::test_support::FakeTraceAllocator> {
        let chunks = (0..blocks)
            .map(|_| Arc::new(Vec::new_in(crate::test_support::FakeTraceAllocator)))
            .collect();
        TraceCacheEntry {
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            sequence_id,
            inits_and_teardowns: None,
            tracing_data: Some(TracingDataHost::Unrolled(
                UnrolledTracingDataHost::NonMemory(ChunkedTraceHolder { chunks }),
            )),
        }
    }

    fn cache(sizes: &[usize]) -> TraceCache<crate::test_support::FakeTraceAllocator> {
        let mut cache = TraceCache::new();
        for (sequence_id, &blocks) in sizes.iter().enumerate() {
            cache.push_back(entry(sequence_id, blocks));
        }
        cache
    }

    #[test]
    fn cpu_block_count_sums_every_entry() {
        assert_eq!(cache(&[]).block_count(), 0);
        assert_eq!(cache(&[3, 4, 5]).block_count(), 12);
    }

    #[test]
    fn cpu_a_cache_within_quota_evicts_nothing() {
        let mut cache = cache(&[3, 4]);
        assert!(cache.evict_to_fit(7).is_empty());
        assert_eq!(cache.entries.len(), 2);
    }

    #[test]
    fn cpu_eviction_takes_whole_entries_oldest_first() {
        let mut cache = cache(&[3, 4, 5]);
        let evicted = cache.evict_to_fit(9);
        assert_eq!(evicted.len(), 1, "evicting the oldest alone gets under 9");
        assert_eq!(evicted[0].sequence_id, 0);
        assert_eq!(cache.block_count(), 9);
    }

    /// The minimum-pool case: every entry is larger than the quota, so an
    /// implementation that refused to evict one would hold blocks forever.
    #[test]
    fn cpu_a_zero_quota_drains_the_cache() {
        let mut cache = cache(&[3, 4, 5]);
        let evicted = cache.evict_to_fit(0);
        assert_eq!(evicted.len(), 3);
        assert_eq!(cache.block_count(), 0);
        assert!(cache.is_empty());
    }

    #[test]
    fn cpu_an_oversized_entry_is_evicted_rather_than_pinned() {
        let mut cache = cache(&[100]);
        let evicted = cache.evict_to_fit(10);
        assert_eq!(evicted.len(), 1);
        assert!(cache.is_empty());
    }
}
