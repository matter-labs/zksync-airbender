//! The responder of the zero-knowledge masking query.
//!
//! The exit sequence `riscv_common::finish_execution_recursion_extended` sends one query,
//! [`ZK_MASKING_QUERY_ID`] with the number of words it is about to read as the input word, and
//! then reads exactly that many words: 4 per register group, then an (address, value) pair per
//! store. The sequence and its parameters are in `riscv_common::zk_masking`; this is the host
//! side, a processor of [`QueryDispatcher`](super::QueryDispatcher).
//!
//! The guest does not check the store addresses: the responder answers with word-aligned
//! addresses outside of ROM and inside the memory that inits/teardowns cover, spread over the
//! chunks of the address space that need their own randomness.

use super::query_ids::ZK_MASKING_QUERY_ID;
use super::{respond_to_every_target, OracleQueryProcessor, QuerierMemory, RunMode};
use rand::rngs::StdRng;
use rand::{CryptoRng, Rng, SeedableRng};
use riscv_common::zk_masking::{
    ADDRESS_CHUNKS, INITS_AND_TEARDOWNS_ROW_BLOCKS, INITS_AND_TEARDOWNS_SETS, MEMORY_WRITES,
    ORACLE_WORDS, ORACLE_WORDS_PER_REGISTER_GROUP, REGISTER_GROUPS,
};

/// The parameters of the guest's masking sequence, for the hosts that check an execution.
pub use riscv_common::zk_masking as parameters;
/// The tail of the exit sequence that sends the masking query.
pub use riscv_common::RECURSION_EXIT_TAIL_SEQUENCE;

const WORD_BYTES: u32 = core::mem::size_of::<u32>() as u32;

/// Memory that the inline inits/teardowns of the proven chunk cover, and the part of it that
/// can not be written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaskingMemoryLayout {
    /// Bytes covered by inits/teardowns, from address 0: both sets of every trace row.
    pub total_init_memory_bytes: u32,
    /// The stores never go below this address.
    pub rom_bytes: u32,
}

impl MaskingMemoryLayout {
    /// 2^22 rows: 32 Mb in 1 Mb chunks. 2^23 rows: 64 Mb in 2 Mb chunks. ROM is the 4 Mb of
    /// the machine (`common_constants::ROM_BYTE_SIZE`), the same as in the linker scripts, so
    /// the 4 (resp. 2) lowest chunks of set 0 get no stores. Their row blocks are still masked:
    /// both sets of a row are multiplied into the same grand product accumulation, and set 1
    /// covers every row block.
    pub const fn for_trace_len_log2(trace_len_log2: u32) -> Self {
        Self {
            total_init_memory_bytes: INITS_AND_TEARDOWNS_SETS * WORD_BYTES << trace_len_log2,
            rom_bytes: common_constants::rom::ROM_BYTE_SIZE as u32,
        }
    }

    const fn set_bytes(&self) -> u32 {
        self.total_init_memory_bytes / INITS_AND_TEARDOWNS_SETS
    }

    const fn chunk_bytes(&self) -> u32 {
        self.total_init_memory_bytes / ADDRESS_CHUNKS
    }

    /// Writable `[start, end)` byte ranges of the chunks of one set, in address order. A chunk
    /// that is ROM as a whole is left out.
    pub fn writable_chunks_of_set(&self, set: u32) -> Vec<(u32, u32)> {
        assert!(set < INITS_AND_TEARDOWNS_SETS);
        assert!(self.total_init_memory_bytes % (ADDRESS_CHUNKS * WORD_BYTES) == 0);
        assert!(self.rom_bytes % WORD_BYTES == 0);
        (0..INITS_AND_TEARDOWNS_ROW_BLOCKS)
            .filter_map(|block| {
                let chunk_start = set * self.set_bytes() + block * self.chunk_bytes();
                let chunk_end = chunk_start + self.chunk_bytes();
                let start = chunk_start.max(self.rom_bytes);
                (start < chunk_end).then_some((start, chunk_end))
            })
            .collect()
    }
}

/// Answers [`ZK_MASKING_QUERY_ID`] with the words that the masking sequence reads.
///
/// The generator must be cryptographically secure, hence the `CryptoRng` bound, and seeded with
/// fresh entropy for every proof: a predictable or reused stream removes the masking entirely.
pub struct MaskingResponder<R: CryptoRng = StdRng> {
    rng: R,
    /// Per set, the writable chunks. Every set keeps its half of the stores, spread evenly over
    /// its writable chunks, so the chunks under ROM cost the set nothing.
    writable_chunks: [Vec<(u32, u32)>; INITS_AND_TEARDOWNS_SETS as usize],
}

impl MaskingResponder<StdRng> {
    pub fn from_os_entropy(layout: MaskingMemoryLayout) -> Self {
        Self::with_rng(layout, StdRng::from_os_rng())
    }
}

impl<R: CryptoRng> MaskingResponder<R> {
    pub fn with_rng(layout: MaskingMemoryLayout, rng: R) -> Self {
        let writable_chunks = core::array::from_fn(|set| layout.writable_chunks_of_set(set as u32));
        for (set, chunks) in writable_chunks.iter().enumerate() {
            assert!(!chunks.is_empty(), "set {} has no writable memory", set);
        }
        Self {
            rng,
            writable_chunks,
        }
    }

    /// The words of one masking stream, in the order the sequence reads them.
    pub fn masking_stream(&mut self) -> Vec<u32> {
        let mut words = Vec::with_capacity(ORACLE_WORDS as usize);
        for _ in 0..REGISTER_GROUPS * ORACLE_WORDS_PER_REGISTER_GROUP {
            words.push(self.rng.next_u32());
        }
        for write_idx in 0..MEMORY_WRITES {
            // alternate between the sets, round-robin over the chunks within a set
            let chunks = &self.writable_chunks[(write_idx % INITS_AND_TEARDOWNS_SETS) as usize];
            let (start, end) =
                chunks[(write_idx / INITS_AND_TEARDOWNS_SETS) as usize % chunks.len()];
            let address = self.rng.random_range(start / WORD_BYTES..end / WORD_BYTES) * WORD_BYTES;
            words.push(address);
            words.push(self.rng.next_u32());
        }
        debug_assert_eq!(words.len(), ORACLE_WORDS as usize);
        words
    }
}

impl<R: CryptoRng> OracleQueryProcessor for MaskingResponder<R> {
    fn supported_memory_query_ids(&self) -> Vec<u32> {
        vec![ZK_MASKING_QUERY_ID]
    }

    fn process_memory_query(
        &mut self,
        query_id: u32,
        input_word: usize,
        _memory: &dyn QuerierMemory,
        mode: RunMode,
        native_run_responses: &mut Vec<u32>,
        guest_run_responses: &mut Vec<u32>,
    ) {
        assert_eq!(query_id, ZK_MASKING_QUERY_ID);
        // the input word is the number of words the sequence reads: a guest built with other
        // masking parameters than this host must not be served a stream of the wrong shape
        assert_eq!(
            input_word, ORACLE_WORDS as usize,
            "the masking sequence of the guest reads {} words, the responder serves {}",
            input_word, ORACLE_WORDS
        );
        respond_to_every_target(
            mode,
            self.masking_stream(),
            native_run_responses,
            guest_run_responses,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::{GuestSource, QueryDispatcher};
    use crate::vm::NonDeterminismCSRSource;
    use riscv_common::zk_masking::MASKING_QUERY_ID;

    const MB: u32 = 1 << 20;

    /// Host model of the guest sequence: the query, then the same reads in the same order.
    /// Returns the addresses of the stores.
    fn model_run(source: &mut GuestSource) -> Vec<u32> {
        let ram = [0u32; 4];
        source.write_with_memory_access(&ram, MASKING_QUERY_ID);
        source.write_with_memory_access(&ram, ORACLE_WORDS);
        for _ in 0..REGISTER_GROUPS {
            for _ in 0..2 {
                let (a, b) = (source.read(), source.read());
                let _ = a.wrapping_add(b) ^ (a << (b & 31)) ^ (b >> (a & 31));
            }
        }
        (0..MEMORY_WRITES)
            .map(|_| {
                let (address, _value) = (source.read(), source.read());
                address
            })
            .collect()
    }

    fn check_layout(trace_len_log2: u32, total_mb: u32, rom_only_chunks: usize) {
        let layout = MaskingMemoryLayout::for_trace_len_log2(trace_len_log2);
        assert_eq!(layout.total_init_memory_bytes, total_mb * MB);
        assert_eq!(layout.rom_bytes, 4 * MB);
        let chunk_bytes = total_mb * MB / ADDRESS_CHUNKS;

        let mut oracle = QueryDispatcher::new(RunMode::RiscVRun);
        oracle.add_external_processor(MaskingResponder::from_os_entropy(layout));
        // an input word that the guest reads after the masking stream
        let mut source = GuestSource::new([0xfeed], oracle);

        let addresses = model_run(&mut source);
        // the response is exactly what the sequence reads, and the inputs are intact
        assert!(!source.oracle.has_pending_response());
        assert_eq!(source.read(), 0xfeed);

        let mut per_chunk = [0u32; ADDRESS_CHUNKS as usize];
        for address in addresses {
            assert_eq!(address % 4, 0);
            assert!(address >= layout.rom_bytes);
            assert!(address < layout.total_init_memory_bytes);
            per_chunk[(address / chunk_bytes) as usize] += 1;
        }
        let half = (ADDRESS_CHUNKS / INITS_AND_TEARDOWNS_SETS) as usize;
        for (set, counts) in per_chunk.chunks(half).enumerate() {
            let writable = if set == 0 {
                half - rom_only_chunks
            } else {
                half
            };
            let expected = MEMORY_WRITES / INITS_AND_TEARDOWNS_SETS / writable as u32;
            for (chunk, count) in counts.iter().enumerate() {
                if set == 0 && chunk < rom_only_chunks {
                    assert_eq!(*count, 0);
                } else {
                    // the split is even up to the remainder of the round-robin
                    assert!(*count == expected || *count == expected + 1);
                }
            }
            assert_eq!(
                counts.iter().sum::<u32>(),
                MEMORY_WRITES / INITS_AND_TEARDOWNS_SETS
            );
        }
    }

    #[test]
    fn stores_are_spread_over_32_mb_for_2_22_trace() {
        check_layout(22, 32, 4);
    }

    #[test]
    fn stores_are_spread_over_64_mb_for_2_23_trace() {
        check_layout(23, 64, 2);
    }

    #[test]
    #[should_panic(expected = "the masking sequence of the guest reads")]
    fn a_guest_with_other_masking_parameters_is_rejected() {
        let layout = MaskingMemoryLayout::for_trace_len_log2(23);
        let mut oracle = QueryDispatcher::new(RunMode::RiscVRun);
        oracle.add_external_processor(MaskingResponder::from_os_entropy(layout));
        let ram = [0u32; 4];
        oracle.write_with_memory_access(&ram, MASKING_QUERY_ID);
        oracle.write_with_memory_access(&ram, ORACLE_WORDS + 2);
    }
}
