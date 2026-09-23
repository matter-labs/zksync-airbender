use crate::upstream::{split_timestamp, split_u32_into_pair_u16, Field, PrimeField, BF};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2};

/// One set's teardown columns: `(.0 = [timestamp low, timestamp high], .1 =
/// [value low, value high])`, each of length `1 << trace_len_log2`.
pub(super) type TeardownColumns = ([Vec<BF>; 2], [Vec<BF>; 2]);

pub(super) fn zero_sets(num_sets: usize, trace_len: usize) -> Vec<TeardownColumns> {
    (0..num_sets)
        .map(|_| {
            (
                [vec![BF::ZERO; trace_len], vec![BF::ZERO; trace_len]],
                [vec![BF::ZERO; trace_len], vec![BF::ZERO; trace_len]],
            )
        })
        .collect()
}

pub(super) fn expand<A: HostTraceAllocator>(
    trace: &InitsAndTeardownsTraceHost<A>,
    num_sets: usize,
    trace_len_log2: u32,
) -> Vec<TeardownColumns> {
    assert_eq!(
        trace.top_bits.len(),
        num_sets,
        "inits-and-teardowns instance carries {} windows, circuit has {num_sets} sets",
        trace.top_bits.len()
    );
    assert!(
        trace_len_log2 >= PAGE_SIZE_LOG2,
        "a set's window ({trace_len_log2} bits) is smaller than one page ({PAGE_SIZE_LOG2} bits)"
    );
    let trace_len = 1usize << trace_len_log2;
    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let page_in_set_mask = (1u32 << pages_per_set_log2) - 1;
    let page_size_words = 1usize << PAGE_SIZE_LOG2;

    let mut sets = zero_sets(num_sets, trace_len);
    // The three streams are page-aligned but chunked independently, so they are
    // walked as flat sequences rather than zipped chunk by chunk.
    let mut values = trace
        .values_packed
        .chunks
        .iter()
        .flat_map(|chunk| chunk.iter().copied());
    let mut timestamps = trace
        .timestamps_packed
        .chunks
        .iter()
        .flat_map(|chunk| chunk.iter().copied());
    for page_index in trace
        .page_indices
        .chunks
        .iter()
        .flat_map(|chunk| chunk.iter().copied())
    {
        let set_idx = (page_index >> pages_per_set_log2) as usize;
        assert!(
            set_idx < num_sets,
            "page index {page_index} selects set {set_idx}, beyond the {num_sets} sets"
        );
        let row_base = ((page_index & page_in_set_mask) as usize) << PAGE_SIZE_LOG2;
        let (timestamp_columns, value_columns) = &mut sets[set_idx];
        for word_in_page in 0..page_size_words {
            let value = values
                .next()
                .expect("values_packed holds one page per page index");
            let timestamp = timestamps
                .next()
                .expect("timestamps_packed holds one page per page index");
            let row = row_base + word_in_page;
            let (timestamp_low, timestamp_high) = split_timestamp(timestamp);
            let (value_low, value_high) = split_u32_into_pair_u16(value);
            timestamp_columns[0][row] = BF::from_u32_unchecked(timestamp_low);
            timestamp_columns[1][row] = BF::from_u32_unchecked(timestamp_high);
            value_columns[0][row] = BF::from_u32_unchecked(value_low as u32);
            value_columns[1][row] = BF::from_u32_unchecked(value_high as u32);
        }
    }
    assert!(
        values.next().is_none() && timestamps.next().is_none(),
        "values/timestamps outlast the page indices they belong to"
    );
    sets
}

#[cfg(test)]
mod tests {
    use super::*;
    use common_constants::TimestampScalar;
    use execution_prover_model::allocator::CpuTraceAllocator;
    use execution_prover_model::trace::ChunkedTraceHolder;
    use riscv_transpiler::vm::{RamWithRomRegion, RAM};
    use std::alloc::Global;
    use std::collections::BTreeMap;
    use std::sync::Arc;

    const PAGE_WORDS: usize = 1 << PAGE_SIZE_LOG2;
    /// Small enough to expand in a unit test, still several pages per set.
    const TRACE_LEN_LOG2: u32 = 12;
    const NUM_SETS: usize = 4;
    const ROM_BOUND_SECOND_WORD_BITS: usize = 1;

    fn chunked<T: Copy>(
        values: &[T],
        chunk_len: usize,
    ) -> ChunkedTraceHolder<T, CpuTraceAllocator> {
        let chunks = values
            .chunks(chunk_len.max(1))
            .map(|chunk| {
                let allocator =
                    CpuTraceAllocator::new(size_of_val(chunk).next_power_of_two().max(4096));
                let mut owned = Vec::with_capacity_in(chunk.len(), allocator);
                owned.extend_from_slice(chunk);
                Arc::new(owned)
            })
            .collect();
        ChunkedTraceHolder { chunks }
    }

    /// Pack `(word address, value, timestamp)` triples the way the producer
    /// does: one page slot per touched page, in ascending page order.
    fn pack(
        touched: &[(u32, u32, TimestampScalar)],
        top_bits: Vec<u32>,
        pages_chunk_len: usize,
        words_chunk_len: usize,
    ) -> InitsAndTeardownsTraceHost<CpuTraceAllocator> {
        let pages_per_set_log2 = TRACE_LEN_LOG2 - PAGE_SIZE_LOG2;
        let mut pages: BTreeMap<u32, (Vec<u32>, Vec<TimestampScalar>)> = BTreeMap::new();
        for (word_idx, value, timestamp) in touched.iter().copied() {
            let global_page = word_idx >> PAGE_SIZE_LOG2;
            let window = global_page >> pages_per_set_log2;
            let set_idx = top_bits
                .iter()
                .position(|w| *w == window)
                .expect("touched word must lie in a scheduled window")
                as u32;
            let local_page =
                (set_idx << pages_per_set_log2) | (global_page & ((1 << pages_per_set_log2) - 1));
            let entry = pages.entry(local_page).or_insert_with(|| {
                (
                    vec![0u32; PAGE_WORDS],
                    vec![0 as TimestampScalar; PAGE_WORDS],
                )
            });
            let word_in_page = (word_idx & ((1 << PAGE_SIZE_LOG2) - 1)) as usize;
            entry.0[word_in_page] = value;
            entry.1[word_in_page] = timestamp;
        }
        let mut page_indices = Vec::new();
        let mut values_packed = Vec::new();
        let mut timestamps_packed = Vec::new();
        for (page_index, (values, timestamps)) in pages {
            page_indices.push(page_index);
            values_packed.extend_from_slice(&values);
            timestamps_packed.extend_from_slice(&timestamps);
        }
        InitsAndTeardownsTraceHost {
            page_indices: chunked(&page_indices, pages_chunk_len),
            values_packed: chunked(&values_packed, words_chunk_len),
            timestamps_packed: chunked(&timestamps_packed, words_chunk_len),
            top_bits,
        }
    }

    /// The independent oracle: write RAM words, let the transpiler collect them
    /// into its own set representation, and require the packed-stream expansion
    /// to agree column for column.
    #[test]
    fn expansion_agrees_with_the_transpiler_collector() {
        let worker = worker::Worker::new_with_num_threads(2);
        let rom_words = 1 << (16 + ROM_BOUND_SECOND_WORD_BITS - 2);
        let total_size_bytes = 1usize << (16 + ROM_BOUND_SECOND_WORD_BITS + 4);
        let mut ram = RamWithRomRegion::<ROM_BOUND_SECOND_WORD_BITS>::from_rom_content(
            &vec![0u32; rom_words],
            total_size_bytes,
        );
        // Only words above the ROM region: the two paths mask ROM differently,
        // and that difference is not what this test is about.
        let first_ram_word = (1usize << (16 + ROM_BOUND_SECOND_WORD_BITS)) / 4;
        let trace_len = 1usize << TRACE_LEN_LOG2;
        let touched_words: Vec<usize> = vec![
            first_ram_word,
            first_ram_word + 1,
            first_ram_word + PAGE_WORDS,
            first_ram_word + trace_len,
            first_ram_word + trace_len + PAGE_WORDS + 5,
            total_size_bytes / 4 - 1,
        ];
        for (index, word) in touched_words.iter().enumerate() {
            ram.write_word(
                (*word as u32) * 4,
                0x0100_0000 + index as u32,
                (index as TimestampScalar + 1) << 4,
            );
        }

        let groups = ram.collect_inits_and_teardowns_sets::<BF, Global>(
            &worker,
            TRACE_LEN_LOG2 as usize,
            NUM_SETS,
            None,
        );
        assert!(!groups.is_empty(), "the collector found no populated set");

        let sparse = ram.collect_inits_and_teardowns(&worker, Global);
        for (top_bits, expected_sets) in groups {
            let touched: Vec<(u32, u32, TimestampScalar)> = sparse
                .iter()
                .flatten()
                .filter_map(|(address, (timestamp, value))| {
                    let word = address >> 2;
                    let window = word >> TRACE_LEN_LOG2;
                    top_bits
                        .contains(&window)
                        .then_some((word, *value, *timestamp))
                })
                .collect();
            let trace = pack(&touched, top_bits.clone(), 3, PAGE_WORDS * 2);
            let actual = expand(&trace, NUM_SETS, TRACE_LEN_LOG2);
            assert_eq!(actual.len(), expected_sets.len());
            for (set_idx, (actual_set, expected_set)) in
                actual.iter().zip(expected_sets.iter()).enumerate()
            {
                assert_eq!(
                    actual_set.0, expected_set.0,
                    "timestamp columns of set {set_idx} (windows {top_bits:?})"
                );
                assert_eq!(
                    actual_set.1, expected_set.1,
                    "value columns of set {set_idx} (windows {top_bits:?})"
                );
            }
        }
    }
}
