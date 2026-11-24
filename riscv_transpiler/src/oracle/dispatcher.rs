//! [`QueryDispatcher`]: dispatches queries to [`OracleQueryProcessor`]s, serves a querier in
//! this process, and serves the RISC-V guest of the simulators (the transpiler-based one and the
//! JIT) as its non-determinism CSR source.
//!
//! Only the memory-based protocol is served: a query is the ID and an input word, the response
//! is raw words. The guest's debug output, QuasiUART frames that start with [`UART_QUERY_ID`],
//! is printed to stderr.

use super::querier_memory::{GuestMemory, NativeQuerierMemory, QuerierMemory};
use super::query_ids::{DISCONNECT_ORACLE_QUERY_ID, UART_QUERY_ID};
use super::query_processor::{OracleQueryProcessor, RunMode};
use crate::abstractions::non_determinism::{UartFrame, UartWrite};
use crate::vm::{NonDeterminismCSRSource, RamPeek};
use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

/// An error of serving a querier in this process: the oracle failed, or the querier did not
/// follow the protocol. The guest has no such channel: for it the same conditions are panics of
/// the simulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QueryError(pub &'static str);

impl core::fmt::Display for QueryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.0)
    }
}

impl core::error::Error for QueryError {}

/// Sized adapter so unsized peekers (`[u32]`, generic `R: ?Sized`) can be passed as
/// `&dyn RamPeek`.
struct PeekRef<'a, R: RamPeek + ?Sized>(&'a R);

impl<R: RamPeek + ?Sized> RamPeek for PeekRef<'_, R> {
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        self.0.peek_word(address)
    }
}

/// An oracle that dispatches memory-based queries to its processors. Adding a processor checks
/// that no two serve the same query ID.
///
/// As the non-determinism CSR source of the simulators, a query is two writes, the ID and the
/// input word, served at once; the guest then reads exactly the response words. A disconnected
/// oracle ([`DISCONNECT_ORACLE_QUERY_ID`]) ignores further queries and answers every read with
/// zero. The source provides no flattened non-determinism: the JIT reads it word by word.
pub struct QueryDispatcher {
    /// The run the oracle serves, which the processors respond for.
    mode: RunMode,
    is_connected: bool,
    /// The processors that serve the queries.
    processors: Vec<Box<dyn OracleQueryProcessor + 'static>>,
    /// Query ID to the index of its processor in `processors`.
    processor_by_query_id: BTreeMap<u32, usize>,
    /// Words of the response to the current query that the querier did not read yet.
    response: VecDeque<u32>,
    /// The response of the RISC-V guest run to the current query of a querier in this process:
    /// the words the guest reads in place of the querier, for a native run that records them
    /// (see [`ReadWitnessSource`]).
    guest_run_response: Vec<u32>,
    /// The query whose input word the guest sends next, when running as the CSR source.
    awaiting_input: Option<u32>,
    /// The guest's debug output in progress.
    uart: UartFrame,
}

impl Default for QueryDispatcher {
    fn default() -> Self {
        Self {
            mode: RunMode::default(),
            is_connected: false,
            processors: Vec::new(),
            processor_by_query_id: BTreeMap::new(),
            response: VecDeque::new(),
            guest_run_response: Vec::new(),
            awaiting_input: None,
            uart: UartFrame::Idle,
        }
    }
}

impl QueryDispatcher {
    /// An oracle without processors for the run `mode` (the default is a native run only).
    pub fn new(mode: RunMode) -> Self {
        let mut source = Self::default();
        source.mode = mode;
        source
    }

    /// The run the oracle serves.
    pub fn run_mode(&self) -> RunMode {
        self.mode
    }

    /// Sets the run the oracle serves, before it serves queries.
    pub fn set_run_mode(&mut self, mode: RunMode) {
        self.mode = mode;
    }

    /// Whether the querier is still connected (no [`DISCONNECT_ORACLE_QUERY_ID`] query yet).
    pub fn is_connected(&self) -> bool {
        self.is_connected
    }

    /// Adds a processor; panics if one of its query IDs already has a processor.
    #[track_caller]
    pub fn add_external_processor<P: OracleQueryProcessor + 'static>(&mut self, processor: P) {
        let processor_id = self.processors.len();
        for id in processor.supported_memory_query_ids() {
            let existing = self.processor_by_query_id.insert(id, processor_id);
            assert!(
                existing.is_none(),
                "more than one processor for query id 0x{id:08x}"
            );
        }
        self.processors.push(Box::new(processor));
        self.is_connected = true;
    }

    /// Serves a query of the querier of the run, and keeps the response for it to read, and in
    /// a native run that records the prover input the response of the RISC-V guest run.
    fn process_memory_query(
        &mut self,
        query_id: u32,
        input_word: usize,
        memory: &dyn QuerierMemory,
    ) -> Result<(), QueryError> {
        let Some(processor_id) = self.processor_by_query_id.get(&query_id).copied() else {
            return Err(QueryError("invalid query ID"));
        };
        let mode = self.mode;
        let mut native_run_responses = Vec::new();
        let mut guest_run_responses = Vec::new();
        let started = query_timing::start();
        self.processors[processor_id].process_memory_query(
            query_id,
            input_word,
            memory,
            mode,
            &mut native_run_responses,
            &mut guest_run_responses,
        );
        query_timing::record(query_id, None, started);
        // the responses of the runs of the mode, and only those
        let responds_for_mode = match mode {
            RunMode::NativeRunOnly => guest_run_responses.is_empty(),
            RunMode::NativeRunSavingForRiscV => {
                native_run_responses.is_empty() == guest_run_responses.is_empty()
            }
            RunMode::RiscVRun => native_run_responses.is_empty(),
        };
        if !responds_for_mode {
            return Err(QueryError(
                "the query processor does not respond for the run mode",
            ));
        }
        match mode {
            RunMode::NativeRunOnly => self.response = native_run_responses.into(),
            RunMode::NativeRunSavingForRiscV => {
                self.response = native_run_responses.into();
                self.guest_run_response = guest_run_responses;
            }
            RunMode::RiscVRun => self.response = guest_run_responses.into(),
        }
        Ok(())
    }

    /// Whether the querier has response words of the current query left to read.
    pub fn has_pending_response(&self) -> bool {
        !self.response.is_empty()
    }

    /// The next word the guest reads from the CSR: the response words of the current query, and
    /// zeroes once disconnected.
    pub fn read_csr_word(&mut self) -> u32 {
        if let Some(word) = self.response.pop_front() {
            return word;
        }
        if !self.is_connected {
            return 0;
        }
        panic!("the guest reads the CSR, but no response is prepared");
    }

    /// A word the guest writes to the CSR: a query ID then its input word (the query is served at
    /// once with `memory`), or a word of a QuasiUART frame.
    pub fn write_csr_word(&mut self, memory: &dyn RamPeek, value: u32) {
        if let Some(query_id) = self.awaiting_input.take() {
            // the input word may be a guest address that the processor reads through while the
            // guest waits
            if query_id == DISCONNECT_ORACLE_QUERY_ID {
                self.is_connected = false;
            } else {
                assert_eq!(
                    self.mode,
                    RunMode::RiscVRun,
                    "the oracle serves a native run, not the RISC-V guest"
                );
                self.process_memory_query(query_id, value as usize, &GuestMemory(memory))
                    .expect("must serve the memory-based query");
            }
            return;
        }
        match self.uart.write(value) {
            UartWrite::NotAFrame => {}
            UartWrite::Consumed => return,
            UartWrite::Complete(message) => {
                eprintln!("{}", String::from_utf8_lossy(&message));
                return;
            }
        }
        if !self.response.is_empty() {
            eprintln!(
                "the response to the previous query is not consumed in full, but received value 0x{value:08x}"
            );
            self.response.clear();
        }
        if value == UART_QUERY_ID {
            self.uart.start();
        } else if !self.is_connected {
            // a disconnected guest's queries are ignored, and read zeroes
        } else if value == DISCONNECT_ORACLE_QUERY_ID
            || self.processor_by_query_id.contains_key(&value)
        {
            self.awaiting_input = Some(value);
        } else {
            panic!(
                "no processor for query ID 0x{value:08x} (only the memory-based protocol is served)"
            );
        }
    }
}

/// The querier runs in this process (forward mode, and the native run that records the prover
/// input). These are the transport primitives of the querier side; the trait that a querier is
/// written against belongs to the querier's crate, and is implemented by delegation to them.
impl QueryDispatcher {
    /// Starts a query: takes the query ID and the input word, and reads whatever the input word
    /// refers to during this call.
    ///
    /// # Safety
    ///
    /// The input word must be what `query_id` defines: a value, or the address of a live input
    /// with the layout that `query_id` defines, whose own pointers reference live values of the
    /// types the query expects, for the duration of the call.
    pub unsafe fn send_query(
        &mut self,
        query_id: u32,
        input_word: usize,
    ) -> Result<(), QueryError> {
        if !self.mode.produces_native_run_responses() {
            return Err(QueryError(
                "the oracle serves the RISC-V guest, not a querier in this process",
            ));
        }
        self.guest_run_response.clear();
        if !self.response.is_empty() {
            self.response.clear();
            return Err(QueryError(
                "previous oracle response was not consumed in full",
            ));
        }
        if query_id == DISCONNECT_ORACLE_QUERY_ID {
            self.is_connected = false;
        }
        if !self.is_connected {
            // as when running as the CSR source, reads return zeroes
            return Ok(());
        }
        // SAFETY: the querier of this process exposes the memory the input word refers to while
        // it sends the query, i.e. during this call
        let memory = unsafe { NativeQuerierMemory::new() };
        self.process_memory_query(query_id, input_word, &memory)
    }

    /// Reads one response word.
    pub fn read_word(&mut self) -> Result<u32, QueryError> {
        match self.response.pop_front() {
            Some(word) => Ok(word),
            None if !self.is_connected => Ok(0),
            None => Err(QueryError("oracle response is shorter than expected")),
        }
    }

    /// Writes the next `num_words` response words to `dst`, in order.
    ///
    /// # Safety
    ///
    /// `dst` must be non-null (even if `num_words` is 0), aligned for `u32` and valid for writes
    /// of `num_words` `u32`s.
    pub unsafe fn write_words(
        &mut self,
        dst: *mut u32,
        num_words: usize,
    ) -> Result<(), QueryError> {
        if self.response.len() < num_words {
            if !self.is_connected {
                // SAFETY: guaranteed by the caller
                unsafe { dst.write_bytes(0, num_words) };
                return Ok(());
            }
            return Err(QueryError("oracle response is shorter than expected"));
        }
        for (i, word) in self.response.drain(..num_words).enumerate() {
            // SAFETY: `i < num_words`, and the caller guarantees `dst` is valid for `num_words`
            // words
            unsafe { dst.add(i).write(word) };
        }
        Ok(())
    }

    /// Ends the query, and checks that the response was consumed in full.
    pub fn finish_query(&mut self) -> Result<(), QueryError> {
        if self.response.is_empty() {
            Ok(())
        } else {
            self.response.clear();
            Err(QueryError("oracle response contains excess data"))
        }
    }
}

/// The non-determinism CSR of the RISC-V guest in the simulators: the transpiler-based one
/// calls `write_with_memory_access`, the JIT that or `write_with_memory_access_raw`; neither
/// gets flattened non-determinism from this source (the default of the trait).
impl NonDeterminismCSRSource for QueryDispatcher {
    fn read(&mut self) -> u32 {
        self.read_csr_word()
    }

    fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, ram: &R, value: u32) {
        self.write_csr_word(&PeekRef(ram), value);
    }

    fn write_with_memory_access_raw(&mut self, ram: &[u32], value: u32) {
        self.write_csr_word(&PeekRef(ram), value);
    }

    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.write_csr_word(ram, value);
    }
}

impl Drop for QueryDispatcher {
    fn drop(&mut self) {
        query_timing::report_and_reset();
    }
}

/// Opt-in accounting of the host time spent answering oracle queries, per query ID and, for
/// processors that report it, per operation inside the query. Enabled by the environment
/// variable `ORACLE_QUERY_TIMING`; the table is printed to stderr when an oracle is dropped.
pub mod query_timing {
    use std::collections::BTreeMap;
    use std::sync::{Mutex, OnceLock};
    use std::time::{Duration, Instant};

    type Key = (u32, Option<u32>);
    static ENABLED: OnceLock<bool> = OnceLock::new();
    static STATS: Mutex<BTreeMap<Key, (u64, Duration)>> = Mutex::new(BTreeMap::new());

    pub fn enabled() -> bool {
        *ENABLED.get_or_init(|| std::env::var_os("ORACLE_QUERY_TIMING").is_some())
    }

    /// The start of a timed section, `None` when the accounting is off
    pub fn start() -> Option<Instant> {
        enabled().then(Instant::now)
    }

    /// Adds the time since `started` to the query `query_id` (`operation` = a kind inside it)
    pub fn record(query_id: u32, operation: Option<u32>, started: Option<Instant>) {
        let Some(started) = started else { return };
        let elapsed = started.elapsed();
        let mut stats = STATS
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let entry = stats.entry((query_id, operation)).or_default();
        entry.0 += 1;
        entry.1 += elapsed;
    }

    pub fn report_and_reset() {
        if !enabled() {
            return;
        }
        let stats = core::mem::take(
            &mut *STATS
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()),
        );
        if stats.is_empty() {
            return;
        }
        let mut rows: Vec<_> = stats.into_iter().collect();
        rows.sort_by_key(|(_, (_, time))| core::cmp::Reverse(*time));
        let total: Duration = rows
            .iter()
            .filter(|((_, operation), _)| operation.is_none())
            .map(|(_, (_, time))| *time)
            .sum();
        eprintln!("oracle query timing, {total:?} in total:");
        for ((query_id, operation), (count, time)) in rows {
            let kind = match operation {
                Some(operation) => format!("0x{query_id:08x} op {operation}"),
                None => format!("0x{query_id:08x}"),
            };
            eprintln!(
                "  {kind:<22} {count:>9} queries {:>12.3} ms {:>10.2} us/query",
                time.as_secs_f64() * 1e3,
                time.as_secs_f64() * 1e6 / count as f64
            );
        }
    }
}

/// Wraps a dispatcher and remembers all the read accesses: the words the guest reads as its
/// non-determinism input when it runs the same computation.
pub struct ReadWitnessSource {
    original_source: QueryDispatcher,
    read_items: Rc<RefCell<Vec<u32>>>,
}

impl ReadWitnessSource {
    pub fn new(original_source: QueryDispatcher) -> Self {
        Self {
            original_source,
            read_items: Rc::new(RefCell::new(vec![])),
        }
    }

    pub fn get_read_items(&self) -> Rc<RefCell<Vec<u32>>> {
        self.read_items.clone()
    }

    /// The wrapped dispatcher.
    pub fn inner(&self) -> &QueryDispatcher {
        &self.original_source
    }
}

impl NonDeterminismCSRSource for ReadWitnessSource {
    fn read(&mut self) -> u32 {
        let item = self.original_source.read();
        // On read - remember the items.
        self.read_items.borrow_mut().push(item);
        item
    }

    fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, ram: &R, value: u32) {
        self.original_source.write_with_memory_access(ram, value);
    }

    fn write_with_memory_access_raw(&mut self, ram: &[u32], value: u32) {
        self.original_source
            .write_with_memory_access_raw(ram, value);
    }

    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.original_source
            .write_with_memory_access_dyn(ram, value);
    }
}

/// Records the responses of the RISC-V guest run, the words the guest reads in place of the
/// querier of this process, which the processors produce along with the responses they serve in
/// the [`RunMode::NativeRunSavingForRiscV`] mode (see
/// [`OracleQueryProcessor::process_memory_query`]). A disconnected oracle does not respond, and
/// the zeroes the querier reads then are recorded as read: the guest reads zeroes then too.
impl ReadWitnessSource {
    /// See [`QueryDispatcher::send_query`].
    ///
    /// # Safety
    ///
    /// As of [`QueryDispatcher::send_query`].
    pub unsafe fn send_query(
        &mut self,
        query_id: u32,
        input_word: usize,
    ) -> Result<(), QueryError> {
        if self.original_source.mode != RunMode::NativeRunSavingForRiscV {
            return Err(QueryError(
                "recording the prover input needs the run mode that saves the responses for the RISC-V guest",
            ));
        }
        // SAFETY: the caller's contract, unchanged
        unsafe { self.original_source.send_query(query_id, input_word)? };
        let guest_run_response = core::mem::take(&mut self.original_source.guest_run_response);
        self.read_items.borrow_mut().extend(guest_run_response);
        Ok(())
    }

    /// See [`QueryDispatcher::read_word`].
    pub fn read_word(&mut self) -> Result<u32, QueryError> {
        let word = self.original_source.read_word()?;
        if !self.original_source.is_connected {
            self.read_items.borrow_mut().push(word);
        }
        Ok(word)
    }

    /// See [`QueryDispatcher::write_words`].
    ///
    /// # Safety
    ///
    /// As of [`QueryDispatcher::write_words`].
    pub unsafe fn write_words(
        &mut self,
        dst: *mut u32,
        num_words: usize,
    ) -> Result<(), QueryError> {
        // SAFETY: guaranteed by the caller
        unsafe { self.original_source.write_words(dst, num_words)? };
        if !self.original_source.is_connected {
            // SAFETY: the words were just written
            let words = unsafe { core::slice::from_raw_parts(dst, num_words) };
            self.read_items.borrow_mut().extend_from_slice(words);
        }
        Ok(())
    }

    /// See [`QueryDispatcher::finish_query`].
    pub fn finish_query(&mut self) -> Result<(), QueryError> {
        self.original_source.finish_query()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::oracle::querier_memory::{read_querier_u32_words_into, read_querier_word};
    use crate::oracle::query_processor::respond_to_every_target;

    type Source = QueryDispatcher;

    /// The querier side of the two sources that serve a querier in this process
    trait NativeQuerier {
        unsafe fn send_query(&mut self, query_id: u32, input_word: usize)
            -> Result<(), QueryError>;
        unsafe fn write_words(&mut self, dst: *mut u32, num_words: usize)
            -> Result<(), QueryError>;
        fn finish_query(&mut self) -> Result<(), QueryError>;
    }

    macro_rules! native_querier {
        ($source:ty) => {
            impl NativeQuerier for $source {
                unsafe fn send_query(
                    &mut self,
                    query_id: u32,
                    input_word: usize,
                ) -> Result<(), QueryError> {
                    // SAFETY: guaranteed by the caller
                    unsafe { <$source>::send_query(self, query_id, input_word) }
                }
                unsafe fn write_words(
                    &mut self,
                    dst: *mut u32,
                    num_words: usize,
                ) -> Result<(), QueryError> {
                    // SAFETY: guaranteed by the caller
                    unsafe { <$source>::write_words(self, dst, num_words) }
                }
                fn finish_query(&mut self) -> Result<(), QueryError> {
                    <$source>::finish_query(self)
                }
            }
        };
    }
    native_querier!(QueryDispatcher);
    native_querier!(ReadWitnessSource);

    const SWAP_QUERY_ID: u32 = 0x1234_0001;

    /// Reads two 8-word values at the addresses of the array at the input word, and answers
    /// them swapped
    struct SwapProcessor;

    impl OracleQueryProcessor for SwapProcessor {
        fn supported_memory_query_ids(&self) -> Vec<u32> {
            vec![SWAP_QUERY_ID]
        }

        fn process_memory_query(
            &mut self,
            query_id: u32,
            input_word: usize,
            memory: &dyn QuerierMemory,
            mode: RunMode,
            native_run_responses: &mut Vec<u32>,
            guest_run_responses: &mut Vec<u32>,
        ) {
            assert_eq!(query_id, SWAP_QUERY_ID);
            let word_size = memory.word_size();
            let a = read_querier_word(memory, input_word).unwrap();
            let b = read_querier_word(memory, input_word + word_size).unwrap();
            let mut response = vec![0u32; 16];
            read_querier_u32_words_into(memory, b, &mut response[..8]).unwrap();
            read_querier_u32_words_into(memory, a, &mut response[8..]).unwrap();
            respond_to_every_target(mode, response, native_run_responses, guest_run_responses);
        }
    }

    const REPRESENTATION_QUERY_ID: u32 = 0x1234_0003;

    /// Echoes the 8 words at the input word, in a representation that depends on the target: as
    /// is for a querier in this process, in reverse order for the guest.
    struct RepresentationProcessor {
        follows_mode: bool,
    }

    impl OracleQueryProcessor for RepresentationProcessor {
        fn supported_memory_query_ids(&self) -> Vec<u32> {
            vec![REPRESENTATION_QUERY_ID]
        }

        fn process_memory_query(
            &mut self,
            query_id: u32,
            input_word: usize,
            memory: &dyn QuerierMemory,
            mode: RunMode,
            native_run_responses: &mut Vec<u32>,
            guest_run_responses: &mut Vec<u32>,
        ) {
            assert_eq!(query_id, REPRESENTATION_QUERY_ID);
            let mut words = [0u32; 8];
            read_querier_u32_words_into(memory, input_word, &mut words).unwrap();
            if !self.follows_mode || mode.produces_native_run_responses() {
                native_run_responses.extend_from_slice(&words);
            }
            if self.follows_mode && mode.produces_guest_run_responses() {
                guest_run_responses.extend(words.iter().rev());
            }
        }
    }

    const REPRESENTATION: RepresentationProcessor = RepresentationProcessor { follows_mode: true };

    fn words(seed: u32) -> [u32; 8] {
        core::array::from_fn(|i| seed.wrapping_add(i as u32))
    }

    /// The swap query of a querier in this process
    fn swap<O: NativeQuerier>(
        oracle: &mut O,
        a: &[u32; 8],
        b: &[u32; 8],
    ) -> Result<[u32; 16], QueryError> {
        let addresses = [
            a.as_ptr().expose_provenance(),
            b.as_ptr().expose_provenance(),
        ];
        // SAFETY: the array of addresses and the operands are alive during the query
        unsafe { oracle.send_query(SWAP_QUERY_ID, addresses.as_ptr().expose_provenance())? };
        let mut response = [0u32; 16];
        // SAFETY: the buffer holds 16 words
        unsafe { oracle.write_words(response.as_mut_ptr(), 16)? };
        oracle.finish_query()?;
        Ok(response)
    }

    /// The echo query of a querier in this process
    fn echo<O: NativeQuerier>(oracle: &mut O, a: &[u32; 8]) -> Result<[u32; 8], QueryError> {
        // SAFETY: the operand is alive during the query
        unsafe { oracle.send_query(REPRESENTATION_QUERY_ID, a.as_ptr().expose_provenance())? };
        let mut response = [0u32; 8];
        // SAFETY: the buffer holds 8 words
        unsafe { oracle.write_words(response.as_mut_ptr(), 8)? };
        oracle.finish_query()?;
        Ok(response)
    }

    /// The guest memory of the tests: `a` at 0x100, `b` at 0x200, and the address array of the
    /// swap query at 0x300
    fn guest_ram(a: &[u32; 8], b: &[u32; 8]) -> [u32; 256] {
        let mut ram = [0u32; 256];
        ram[0x40..0x48].copy_from_slice(a);
        ram[0x80..0x88].copy_from_slice(b);
        ram[0xc0] = 0x100;
        ram[0xc1] = 0x200;
        ram
    }

    #[test]
    fn memory_queries_in_process_record_the_words_the_guest_reads() {
        let mut oracle = Source::new(RunMode::NativeRunSavingForRiscV);
        oracle.add_external_processor(SwapProcessor);
        let mut source = ReadWitnessSource::new(oracle);
        let (a, b) = (words(1), words(100));
        assert_eq!(
            swap(&mut source, &a, &b),
            Ok([b, a].concat().try_into().unwrap())
        );
        assert_eq!(*source.get_read_items().borrow(), [b, a].concat());
    }

    /// Through every entry point of the simulators' trait
    #[test]
    fn memory_queries_as_the_csr_source_of_the_guest() {
        let mut oracle = Source::new(RunMode::RiscVRun);
        oracle.add_external_processor(SwapProcessor);
        let (a, b) = (words(1), words(100));
        let ram = guest_ram(&a, &b);
        let expected = [b, a].concat();

        // a query is the ID and the input word, then exactly the response words
        oracle.write_with_memory_access(&ram, SWAP_QUERY_ID);
        oracle.write_with_memory_access(&ram, 0x300);
        let response: Vec<u32> = (0..16).map(|_| oracle.read()).collect();
        assert_eq!(response, expected);

        // the JIT's minimal tracer writes through a raw slice
        oracle.write_with_memory_access_raw(&ram, SWAP_QUERY_ID);
        oracle.write_with_memory_access_raw(&ram, 0x300);
        let response: Vec<u32> = (0..16).map(|_| oracle.read()).collect();
        assert_eq!(response, expected);

        oracle.write_with_memory_access_dyn(&ram, SWAP_QUERY_ID);
        oracle.write_with_memory_access_dyn(&ram, 0x300);
        let response: Vec<u32> = (0..16).map(|_| oracle.read()).collect();
        assert_eq!(response, expected);

        // no flattened non-determinism: the simulators read word by word
        const { assert!(!Source::PROVIDES_FLATTENED_NON_DETERMINISM) };
        assert!(oracle.nondeterminism_as_raw_ptr().is_none());
    }

    /// The dispatcher is a source for the JIT's context too (its minimal tracer erases the same
    /// trait through `read` and `write_with_memory_access_raw`, covered above), not only for the
    /// transpiler-based simulator
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn fits_the_jit_context() {
        let mut oracle = Source::new(RunMode::RiscVRun);
        oracle.add_external_processor(SwapProcessor);
        let _context = crate::jit::DefaultContextImpl::new(&mut oracle);
    }

    /// A QuasiUART frame between queries is the guest's debug output, not a query
    #[test]
    fn uart_frames_are_not_queries() {
        let mut oracle = Source::new(RunMode::RiscVRun);
        oracle.add_external_processor(SwapProcessor);
        let (a, b) = (words(1), words(100));
        let ram = guest_ram(&a, &b);
        // "hello": 5 bytes in 2 words, after the word count (the length word included)
        for word in [
            UART_QUERY_ID,
            3,
            5,
            u32::from_le_bytes(*b"hell"),
            u32::from_le_bytes(*b"o\0\0\0"),
        ] {
            oracle.write_with_memory_access(&ram, word);
        }
        // an empty frame
        for word in [UART_QUERY_ID, 0] {
            oracle.write_with_memory_access(&ram, word);
        }
        oracle.write_with_memory_access(&ram, SWAP_QUERY_ID);
        oracle.write_with_memory_access(&ram, 0x300);
        let response: Vec<u32> = (0..16).map(|_| oracle.read()).collect();
        assert_eq!(response, [b, a].concat());
    }

    #[test]
    #[should_panic(expected = "no processor for query ID 0x0000abcd")]
    fn an_unknown_query_id_is_rejected_at_once() {
        let mut oracle = Source::new(RunMode::RiscVRun);
        oracle.add_external_processor(SwapProcessor);
        let ram = [0u32; 16];
        oracle.write_with_memory_access(&ram, 0xabcd);
    }

    #[test]
    fn a_disconnected_guest_is_ignored_and_reads_zeroes() {
        let mut oracle = Source::new(RunMode::RiscVRun);
        oracle.add_external_processor(SwapProcessor);
        let ram = [0u32; 16];
        oracle.write_with_memory_access(&ram, DISCONNECT_ORACLE_QUERY_ID);
        oracle.write_with_memory_access(&ram, 0);
        assert!(!oracle.is_connected());
        oracle.write_with_memory_access(&ram, 0xabcd);
        oracle.write_with_memory_access(&ram, SWAP_QUERY_ID);
        assert_eq!(oracle.read(), 0);
    }

    fn reversed(value: &[u32; 8]) -> [u32; 8] {
        let mut words = *value;
        words.reverse();
        words
    }

    #[test]
    fn a_native_run_is_served_its_responses_and_records_those_of_the_guest_run() {
        let (a, b) = (words(1), words(100));

        let mut oracle = Source::new(RunMode::NativeRunOnly);
        oracle.add_external_processor(REPRESENTATION);
        assert_eq!(echo(&mut oracle, &a), Ok(a));

        let mut oracle = Source::new(RunMode::NativeRunSavingForRiscV);
        oracle.add_external_processor(REPRESENTATION);
        oracle.add_external_processor(SwapProcessor);
        let mut source = ReadWitnessSource::new(oracle);
        assert_eq!(echo(&mut source, &a), Ok(a));
        // a response that is the same on every target
        assert_eq!(
            swap(&mut source, &a, &b),
            Ok([b, a].concat().try_into().unwrap())
        );
        let expected = [reversed(&a), b, a].concat();
        assert_eq!(*source.get_read_items().borrow(), expected);
    }

    #[test]
    fn the_guest_is_served_the_responses_of_the_guest_run() {
        let mut oracle = Source::new(RunMode::RiscVRun);
        oracle.add_external_processor(REPRESENTATION);
        let a = words(1);
        let ram = guest_ram(&a, &words(0));
        oracle.write_with_memory_access(&ram, REPRESENTATION_QUERY_ID);
        oracle.write_with_memory_access(&ram, 0x100);
        let response: Vec<u32> = (0..8).map(|_| oracle.read()).collect();
        assert_eq!(response, reversed(&a));
    }

    #[test]
    fn recording_needs_the_mode_that_saves_the_responses_of_the_guest_run() {
        let mut oracle = Source::new(RunMode::NativeRunOnly);
        oracle.add_external_processor(SwapProcessor);
        let mut source = ReadWitnessSource::new(oracle);
        let a = words(1);
        assert!(swap(&mut source, &a, &a).is_err());
        assert!(source.get_read_items().borrow().is_empty());
    }

    #[test]
    fn a_processor_that_does_not_respond_for_the_mode_is_rejected() {
        let mut oracle = Source::new(RunMode::NativeRunSavingForRiscV);
        oracle.add_external_processor(RepresentationProcessor {
            follows_mode: false,
        });
        oracle.add_external_processor(SwapProcessor);
        let mut source = ReadWitnessSource::new(oracle);
        let a = words(1);
        assert_eq!(
            echo(&mut source, &a),
            Err(QueryError(
                "the query processor does not respond for the run mode"
            ))
        );
        // the failed query is over
        assert_eq!(
            swap(&mut source, &a, &a),
            Ok([a, a].concat().try_into().unwrap())
        );
        assert_eq!(*source.get_read_items().borrow(), [a, a].concat());
    }

    #[test]
    fn a_querier_in_this_process_is_not_served_in_a_risc_v_run() {
        let mut oracle = Source::new(RunMode::RiscVRun);
        oracle.add_external_processor(REPRESENTATION);
        assert!(echo(&mut oracle, &words(1)).is_err());
    }

    #[test]
    #[should_panic(expected = "not the RISC-V guest")]
    fn the_guest_is_not_served_in_a_native_run() {
        let mut oracle = Source::new(RunMode::NativeRunSavingForRiscV);
        oracle.add_external_processor(REPRESENTATION);
        let ram = [0u32; 128];
        oracle.write_with_memory_access(&ram, REPRESENTATION_QUERY_ID);
        oracle.write_with_memory_access(&ram, 0x100);
    }

    #[test]
    fn a_disconnected_oracle_records_the_zeroes_read() {
        let mut oracle = Source::new(RunMode::NativeRunSavingForRiscV);
        oracle.add_external_processor(REPRESENTATION);
        let mut source = ReadWitnessSource::new(oracle);
        // SAFETY: the disconnect query has no input
        unsafe { source.send_query(DISCONNECT_ORACLE_QUERY_ID, 0) }.unwrap();
        source.finish_query().unwrap();
        assert!(!source.inner().is_connected());
        assert_eq!(echo(&mut source, &words(1)), Ok([0; 8]));
        assert_eq!(*source.get_read_items().borrow(), vec![0; 8]);
    }

    #[test]
    #[should_panic(expected = "more than one processor")]
    fn a_query_id_has_one_processor() {
        let mut oracle = Source::default();
        oracle.add_external_processor(SwapProcessor);
        oracle.add_external_processor(SwapProcessor);
    }
}
