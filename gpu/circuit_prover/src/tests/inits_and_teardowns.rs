use super::*;
use std::alloc::Global;

/// Bucket sparse `(addr, (timestamp, value))` triples (per CPU-worker chunks) into the
/// page-based SoA wire format consumed by the GPU inits-and-teardowns kernel.
pub(super) fn build_inits_and_teardowns_pages_for_selected_sets_for_test(
    sparse: &[Vec<(u32, (common_constants::TimestampScalar, u32))>],
    trace_len_log2: u32,
    selected_set_top_bits: &[u32],
) -> (Vec<u32>, Vec<u32>, Vec<common_constants::TimestampScalar>) {
    use std::collections::BTreeMap;

    assert!(PAGE_SIZE_LOG2 < trace_len_log2);
    let page_size = 1usize << PAGE_SIZE_LOG2;
    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let pages_per_set_mask = (1u32 << pages_per_set_log2) - 1;

    let mut pages: BTreeMap<u32, (Vec<u32>, Vec<common_constants::TimestampScalar>)> =
        BTreeMap::new();
    for chunk in sparse {
        for &(address, (timestamp, value)) in chunk {
            let word_idx = address >> 2;
            let global_page_idx = word_idx >> PAGE_SIZE_LOG2;
            let global_set_top_bits = global_page_idx >> pages_per_set_log2;
            let local_set_idx = selected_set_top_bits
                .iter()
                .position(|&top_bits| top_bits == global_set_top_bits)
                .unwrap_or_else(|| {
                    panic!(
                        "test producer emitted page_idx {global_page_idx} from global set {global_set_top_bits}, which is absent from selected set top bits {selected_set_top_bits:?}",
                    )
                }) as u32;
            let page_idx =
                (local_set_idx << pages_per_set_log2) | (global_page_idx & pages_per_set_mask);
            let word_in_page = (word_idx & ((1u32 << PAGE_SIZE_LOG2) - 1)) as usize;
            let entry = pages
                .entry(page_idx)
                .or_insert_with(|| (vec![0u32; page_size], vec![0u64; page_size]));
            entry.0[word_in_page] = value;
            entry.1[word_in_page] = timestamp;
        }
    }

    let num_pages = pages.len();
    let mut page_indices = Vec::with_capacity(num_pages);
    let mut values_packed = Vec::with_capacity(num_pages * page_size);
    let mut timestamps_packed = Vec::with_capacity(num_pages * page_size);
    for (page_idx, (vals, tss)) in pages {
        page_indices.push(page_idx);
        values_packed.extend_from_slice(&vals);
        timestamps_packed.extend_from_slice(&tss);
    }
    (page_indices, values_packed, timestamps_packed)
}

#[test]
fn cpu_selected_noncontiguous_sets_are_rebased_into_local_page_geometry() {
    let trace_len_log2 = PAGE_SIZE_LOG2 + 2;
    let selected_set_top_bits = [0, 2];
    let global_page_in_selected_set = 3u32;
    let word_in_page = 7u32;
    let global_word_idx = (selected_set_top_bits[1] << trace_len_log2)
        | (global_page_in_selected_set << PAGE_SIZE_LOG2)
        | word_in_page;
    let timestamp = 11;
    let value = 13;
    let sparse = vec![vec![(global_word_idx << 2, (timestamp, value))]];

    let (page_indices, values_packed, timestamps_packed) =
        build_inits_and_teardowns_pages_for_selected_sets_for_test(
            &sparse,
            trace_len_log2,
            &selected_set_top_bits,
        );

    let pages_per_set_log2 = trace_len_log2 - PAGE_SIZE_LOG2;
    let expected_local_page = (1 << pages_per_set_log2) | global_page_in_selected_set;
    assert_eq!(page_indices, [expected_local_page]);
    assert_eq!(values_packed[word_in_page as usize], value);
    assert_eq!(timestamps_packed[word_in_page as usize], timestamp);
}

pub(super) fn build_inits_and_teardowns_trace_host_for_test(
    page_indices: &[u32],
    values_packed: &[u32],
    timestamps_packed: &[common_constants::TimestampScalar],
    top_bits: &[u32],
) -> InitsAndTeardownsTraceHost<Global> {
    InitsAndTeardownsTraceHost {
        top_bits: top_bits.to_vec(),
        page_indices: ChunkedTraceHolder {
            chunks: vec![Arc::new(page_indices.to_vec())],
        },
        values_packed: ChunkedTraceHolder {
            chunks: vec![Arc::new(values_packed.to_vec())],
        },
        timestamps_packed: ChunkedTraceHolder {
            chunks: vec![Arc::new(timestamps_packed.to_vec())],
        },
    }
}
