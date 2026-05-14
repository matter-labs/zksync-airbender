use std::collections::VecDeque;

use crate::execution::messages::SimulationResult;
use crate::execution::A;
use crate::primitives::circuit_type::CircuitType;
use crate::prover::trace::tracing_data::TracingDataHost;
use crate::witness::trace_unrolled::InitsAndTeardownsTraceHost;

pub(super) struct TraceCacheEntry {
    pub circuit_type: CircuitType,
    pub sequence_id: usize,
    pub inits_and_teardowns: Option<InitsAndTeardownsTraceHost>,
    pub tracing_data: Option<TracingDataHost<A>>,
}

#[derive(Default)]
pub(super) struct TraceCache {
    pub(super) entries: VecDeque<TraceCacheEntry>,
    pub(super) total_requests_count: usize,
    pub(super) trivial_unified_inits_and_teardowns_count: usize,
    pub(super) simulation_result: Option<SimulationResult>,
}

impl TraceCache {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn push_back(&mut self, entry: TraceCacheEntry) {
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
