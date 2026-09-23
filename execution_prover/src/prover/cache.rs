use std::collections::VecDeque;

use crate::messages::SimulationResult;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, TracingDataHost};
use fft::GoodAllocator;

pub(super) struct TraceCacheEntry<A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost<A>>,
    pub tracing_data: Option<TracingDataHost<A>>,
}

#[derive(Default)]
pub(super) struct TraceCache<A: GoodAllocator> {
    pub(super) entries: VecDeque<TraceCacheEntry<A>>,
    pub(super) total_requests_count: usize,
    pub(super) trivial_unified_inits_and_teardowns_count: usize,
    pub(super) simulation_result: Option<SimulationResult>,
}

impl<A: GoodAllocator> TraceCache<A> {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn push_back(&mut self, entry: TraceCacheEntry<A>) {
        self.entries.push_back(entry);
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
