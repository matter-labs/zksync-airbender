//! [`GuestSource`]: the non-determinism CSR source of a guest that takes plain input words and
//! sends queries.

use super::dispatcher::QueryDispatcher;
use crate::vm::{NonDeterminismCSRSource, RamPeek};
use std::collections::VecDeque;

/// The CSR source of the guest: its input words, then the oracle. A read is a word of the
/// response to the current query while there is one, and the next input word otherwise, so the
/// guest may read its inputs before, between and after its queries. Every write goes to the
/// oracle.
///
/// Like the dispatcher, it provides no flattened non-determinism: a consumer that reads a
/// buffer directly would bypass the dispatch.
pub struct GuestSource {
    pub inputs: VecDeque<u32>,
    pub oracle: QueryDispatcher,
}

impl GuestSource {
    pub fn new(inputs: impl IntoIterator<Item = u32>, oracle: QueryDispatcher) -> Self {
        Self {
            inputs: inputs.into_iter().collect(),
            oracle,
        }
    }
}

impl NonDeterminismCSRSource for GuestSource {
    fn read(&mut self) -> u32 {
        if self.oracle.has_pending_response() {
            return self.oracle.read();
        }
        match self.inputs.pop_front() {
            Some(word) => word,
            None => self.oracle.read(),
        }
    }

    fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, ram: &R, value: u32) {
        self.oracle.write_with_memory_access(ram, value);
    }

    fn write_with_memory_access_raw(&mut self, ram: &[u32], value: u32) {
        self.oracle.write_with_memory_access_raw(ram, value);
    }

    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.oracle.write_with_memory_access_dyn(ram, value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::{OracleQueryProcessor, QuerierMemory, RunMode};

    const COUNT_QUERY_ID: u32 = 0x1234_0002;

    /// Answers the input word and the two words after it
    struct CountProcessor;

    impl OracleQueryProcessor for CountProcessor {
        fn supported_memory_query_ids(&self) -> Vec<u32> {
            vec![COUNT_QUERY_ID]
        }

        fn process_memory_query(
            &mut self,
            _query_id: u32,
            input_word: usize,
            _memory: &dyn QuerierMemory,
            _mode: RunMode,
            _native_run_responses: &mut Vec<u32>,
            guest_run_responses: &mut Vec<u32>,
        ) {
            guest_run_responses.extend((0..3).map(|i| input_word as u32 + i));
        }
    }

    #[test]
    fn inputs_and_responses_are_interleaved_by_the_queries() {
        let mut oracle = QueryDispatcher::new(RunMode::RiscVRun);
        oracle.add_external_processor(CountProcessor);
        let mut source = GuestSource::new([1, 2, 3], oracle);
        let ram = [0u32; 4];

        assert_eq!(source.read(), 1);
        source.write_with_memory_access(&ram, COUNT_QUERY_ID);
        source.write_with_memory_access(&ram, 100);
        // the response comes before the remaining inputs
        assert_eq!(
            [source.read(), source.read(), source.read()],
            [100, 101, 102]
        );
        assert_eq!([source.read(), source.read()], [2, 3]);
        assert!(source.inputs.is_empty());
        assert!(!source.oracle.has_pending_response());
    }
}
