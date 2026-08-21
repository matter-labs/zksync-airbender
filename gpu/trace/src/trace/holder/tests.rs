use std::alloc::Global;

use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use era_cudart::memory::memory_copy_async;
use era_cudart::memory::DeviceAllocation as RawDeviceAllocation;

use itertools::Itertools;

use worker::Worker;

use super::*;
use crate::upstream::{
    multivariate_coeffs_into_hypercube_evals, Blake2sU32MerkleTreeWithCap,
    ColumnMajorMerkleTreeConstructor, Field, MerkleTreeCapVarLength, PathQueriable, PrimeField,
};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContextConfig;

// Local test-context builder for the `gpu_trace` suites. Mirrors the apex
// `prover::test_utils::make_test_context` minus its GKR `configure_kernel_
// attributes()` call, which only sets shared-memory carveout on the
// `ab_gkr_main_round*` flat kernels — irrelevant to these trace-holder tests
// and unreachable from this crate. See task-8 report (manifest gap).
const TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

fn make_test_context(
    max_device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
) -> ProverContext {
    let default_block_log_size = ProverContextConfig::default().allocator_block_log_size;
    let arena_bytes = max_device_allocation_blocks_count << default_block_log_size;
    let test_blocks_count = arena_bytes >> TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    let mut config = ProverContextConfig {
        allocator_block_log_size: TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
        max_device_allocation_blocks_count: Some(test_blocks_count),
        ..Default::default()
    };
    let host_block_size = 1usize << config.host_allocator_block_log_size;
    config.host_allocator_blocks_count = (host_pool_size_mb * 1024 * 1024) / host_block_size;
    // Disable the small sub-allocator when the block size is too small for it.
    if config
        .small_allocator_log_chunk_size
        .is_some_and(|s| s >= TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE)
    {
        config.small_allocator_log_chunk_size = None;
    }
    ProverContext::new(&config).unwrap()
}

fn cpu_all_cosets(coeffs: &[BF], log_lde_factor: u32, worker: &Worker) -> Vec<Vec<BF>> {
    let n = coeffs.len();
    let log_n = n.trailing_zeros();
    let twiddles = fft::Twiddles::<BF, Global>::new(n, worker);
    let selected_twiddles = &twiddles.forward_twiddles[..(n >> 1)];
    let tau = fft::domain_generator_for_size::<BF>(1u64 << (log_n + log_lde_factor));
    let mut result = Vec::with_capacity(1 << log_lde_factor);
    for coset_index in 0..(1usize << log_lde_factor) {
        let mut evals = coeffs.to_vec();
        if coset_index != 0 {
            fft::distribute_powers_serial(&mut evals, BF::ONE, tau.pow(coset_index as u32));
        }
        fft::bitreverse_enumeration_inplace(&mut evals);
        fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut evals, log_n, selected_twiddles);
        result.push(evals);
    }
    result
}

fn make_source_host_and_cpu_cosets(
    log_domain_size: u32,
    log_lde_factor: u32,
    columns_count: usize,
    worker: &Worker,
) -> (Vec<BF>, Vec<Vec<BF>>) {
    let domain_size = 1usize << log_domain_size;
    let lde_factor = 1usize << log_lde_factor;
    let mut cpu_columns = Vec::with_capacity(columns_count);
    let mut source_host = vec![BF::ZERO; columns_count * domain_size];
    for column in 0..columns_count {
        let coeffs = (0..domain_size)
            .map(|idx| BF::new((1 + column * domain_size + idx) as u32))
            .collect_vec();
        let mut source_column = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut source_column, log_domain_size);
        fft::bitreverse_enumeration_inplace(&mut source_column);
        source_host[column * domain_size..(column + 1) * domain_size]
            .copy_from_slice(&source_column);
        cpu_columns.push(coeffs);
    }

    let mut cpu_cosets = vec![vec![BF::ZERO; columns_count * domain_size]; lde_factor];
    for (column_idx, coeffs) in cpu_columns.iter().enumerate() {
        for (coset_idx, coset) in cpu_all_cosets(coeffs, log_lde_factor, worker)
            .into_iter()
            .enumerate()
        {
            cpu_cosets[coset_idx][column_idx * domain_size..(column_idx + 1) * domain_size]
                .copy_from_slice(&coset);
        }
    }

    (source_host, cpu_cosets)
}

fn stage1_caps_from_cpu_cosets(
    cpu_cosets: &[Vec<BF>],
    domain_size: usize,
    columns_count: usize,
    rows_per_leaf: usize,
    total_cap_size: usize,
    log_lde_factor: u32,
    worker: &Worker,
) -> Vec<MerkleTreeCapVarLength> {
    let source_storage: Vec<Vec<&[BF]>> = cpu_cosets
        .iter()
        .map(|coset| {
            (0..columns_count)
                .map(|column| &coset[column * domain_size..(column + 1) * domain_size])
                .collect_vec()
        })
        .collect_vec();
    let source_refs = source_storage
        .iter()
        .map(|columns| columns.as_slice())
        .collect_vec();
    let tree = <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
            BF,
        >>::construct_from_cosets::<BF>(
            &source_refs,
            rows_per_leaf,
            total_cap_size,
            true,
            true,
            false,
            worker,
        );
    let subcap_size = total_cap_size >> log_lde_factor;
    PathQueriable::get_cap(&tree)
        .cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec()
}

fn hash_leaf_words(words: &[u32]) -> Digest {
    let num_full_rounds = words.len() / BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let remainder = words.len() % BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let only_full_rounds = remainder == 0;
    let (chunks, tail) = words.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
    let mut state = Blake2sState::new();
    let mut digest = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    for (round_idx, block) in chunks.iter().enumerate() {
        let is_last_round = round_idx + 1 == num_full_rounds;
        if is_last_round && only_full_rounds {
            state.absorb_final_block::<true>(block, BLAKE2S_BLOCK_SIZE_U32_WORDS, &mut digest);
        } else {
            state.absorb::<true>(block);
        }
    }
    if !only_full_rounds {
        let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        block[..tail.len()].copy_from_slice(tail);
        state.absorb_final_block::<true>(&block, tail.len(), &mut digest);
    }

    digest
}

fn extract_query_leaf_words(
    leafs: &[BF],
    query_index: usize,
    queries_count: usize,
    rows_per_leaf: usize,
) -> Vec<u32> {
    let values_per_column_count = queries_count * rows_per_leaf;
    assert_eq!(leafs.len() % values_per_column_count, 0);
    let columns_count = leafs.len() / values_per_column_count;
    let mut result = Vec::with_capacity(columns_count * rows_per_leaf);
    for column in 0..columns_count {
        let start = column * values_per_column_count + query_index * rows_per_leaf;
        result.extend(
            leafs[start..start + rows_per_leaf]
                .iter()
                .map(|value| value.as_u32_raw_repr_reduced()),
        );
    }

    result
}

fn verify_query_against_stage1_caps(
    leaf_words: &[u32],
    merkle_path: &[Digest],
    natural_leaf_index: usize,
    natural_coset_index: usize,
    stage1_caps: &[MerkleTreeCapVarLength],
    log_lde_factor: u32,
) {
    let mut current = hash_leaf_words(leaf_words);
    let mut index = natural_leaf_index;
    for sibling in merkle_path.iter() {
        let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        if index & 1 == 0 {
            block[..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(&current);
            block[BLAKE2S_DIGEST_SIZE_U32_WORDS..].copy_from_slice(sibling);
        } else {
            block[..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(sibling);
            block[BLAKE2S_DIGEST_SIZE_U32_WORDS..].copy_from_slice(&current);
        }
        Blake2sState::compress_two_to_one::<true>(&block, &mut current);
        index >>= 1;
    }

    let stage1_coset_index = super::bitreverse_index(natural_coset_index, log_lde_factor);
    assert_eq!(current, stage1_caps[stage1_coset_index].cap[index]);
}

fn assert_trace_holder_materialization_and_caps_match_cpu(log_rows_per_leaf: u32) {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = PARTIAL_TREE_REDUCTION_LAYERS + 3;
    let log_lde_factor = 2u32;
    let domain_size = 1usize << log_domain_size;
    let columns_count = 3usize;
    let (source_host, cpu_cosets) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);

    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut trace_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_lde_factor + 1,
        columns_count,
        TreesCacheMode::CacheFull,
        &context,
    )
    .unwrap();
    trace_holder
        .materialize_from_hypercube_evals(&source_device, &context)
        .unwrap();
    let mut raw_hypercube = vec![BF::ZERO; source_host.len()];
    memory_copy_async(
        &mut raw_hypercube,
        trace_holder.get_hypercube_evals(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(raw_hypercube, source_host);
    assert!(trace_holder.are_cosets_materialized());

    match &trace_holder.cosets {
        CosetsHolder::Full(backing) => {
            let per_coset = backing.len() / (1usize << log_lde_factor);
            for coset_idx in 0..(1usize << log_lde_factor) {
                let segment = &backing[coset_idx * per_coset..(coset_idx + 1) * per_coset];
                let mut gpu = vec![BF::ZERO; per_coset];
                memory_copy_async(&mut gpu, segment, context.get_exec_stream()).unwrap();
                context.get_exec_stream().synchronize().unwrap();
                let expected = bitreverse_coset_columns(
                    &cpu_cosets[coset_idx],
                    1,
                    columns_count,
                    log_domain_size,
                );
                assert_eq!(gpu, expected, "coset {}", coset_idx);
            }
        }
        CosetsHolder::None(_) => panic!("expected Full cosets in test"),
    }

    trace_holder.commit_all(&context).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let gpu_caps = trace_holder
        .read_per_coset_caps_synchronously(&context)
        .unwrap();
    let cpu_caps = stage1_caps_from_cpu_cosets(
        &cpu_cosets,
        domain_size,
        columns_count,
        1 << log_rows_per_leaf,
        1 << trace_holder.log_tree_cap_size,
        log_lde_factor,
        &worker,
    );
    assert_eq!(gpu_caps, cpu_caps);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_lazy_coset_materialization_matches_cpu() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = PARTIAL_TREE_REDUCTION_LAYERS + 3;
    let log_lde_factor = 2u32;
    let columns_count = 3usize;
    let (source_host, cpu_cosets) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);

    let mut trace_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        0,
        log_lde_factor + 1,
        columns_count,
        TreesCacheMode::CachePartial,
        &context,
    )
    .unwrap();
    memory_copy_async(
        trace_holder.get_uninit_hypercube_evals_mut(),
        &source_host,
        context.get_exec_stream(),
    )
    .unwrap();

    let mut raw_hypercube = vec![BF::ZERO; source_host.len()];
    memory_copy_async(
        &mut raw_hypercube,
        trace_holder.get_hypercube_evals(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(raw_hypercube, source_host);
    assert!(!trace_holder.are_cosets_materialized());

    trace_holder.ensure_cosets_materialized(&context).unwrap();
    assert!(trace_holder.are_cosets_materialized());

    match &trace_holder.cosets {
        CosetsHolder::Full(backing) => {
            let per_coset = backing.len() / (1usize << log_lde_factor);
            for coset_idx in 0..(1usize << log_lde_factor) {
                let segment = &backing[coset_idx * per_coset..(coset_idx + 1) * per_coset];
                let mut gpu = vec![BF::ZERO; per_coset];
                memory_copy_async(&mut gpu, segment, context.get_exec_stream()).unwrap();
                context.get_exec_stream().synchronize().unwrap();
                let expected = bitreverse_coset_columns(
                    &cpu_cosets[coset_idx],
                    1,
                    columns_count,
                    log_domain_size,
                );
                assert_eq!(gpu, expected, "coset {}", coset_idx);
            }
        }
        CosetsHolder::None(_) => panic!("expected Full cosets in test"),
    }
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_cosets_view_is_contiguous_in_coset_major_order() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = PARTIAL_TREE_REDUCTION_LAYERS + 3;
    let log_lde_factor = 2u32;
    let columns_count = 3usize;
    let lde_factor = 1usize << log_lde_factor;
    let per_coset_len = columns_count * (1usize << log_domain_size);

    let (source_host, cpu_cosets) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);

    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut trace_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        0,
        log_lde_factor + 1,
        columns_count,
        TreesCacheMode::CacheNone,
        &context,
    )
    .unwrap();
    trace_holder
        .materialize_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let mut concat = vec![BF::ZERO; lde_factor * per_coset_len];
    for coset_index in 0..lde_factor {
        let coset = trace_holder.get_coset_evaluations(coset_index);
        let dst = &mut concat[coset_index * per_coset_len..(coset_index + 1) * per_coset_len];
        memory_copy_async(dst, coset, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();

    for coset_index in 0..lde_factor {
        let segment = &concat[coset_index * per_coset_len..(coset_index + 1) * per_coset_len];
        let expected =
            bitreverse_coset_columns(&cpu_cosets[coset_index], 1, columns_count, log_domain_size);
        assert_eq!(segment, &expected[..], "coset {coset_index}");
    }
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_consolidated_cosets_matches_per_coset_views() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = PARTIAL_TREE_REDUCTION_LAYERS + 3;
    let log_lde_factor = 2u32;
    let columns_count = 3usize;
    let lde_factor = 1usize << log_lde_factor;
    let per_coset_len = columns_count * (1usize << log_domain_size);

    let (source_host, _) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);

    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut trace_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        0,
        log_lde_factor + 1,
        columns_count,
        TreesCacheMode::CacheNone,
        &context,
    )
    .unwrap();
    trace_holder
        .materialize_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let consolidated = trace_holder.get_consolidated_cosets();
    assert_eq!(consolidated.len(), lde_factor * per_coset_len);

    let mut host_consolidated = vec![BF::ZERO; consolidated.len()];
    memory_copy_async(
        &mut host_consolidated,
        consolidated,
        context.get_exec_stream(),
    )
    .unwrap();

    let mut host_per_coset = vec![BF::ZERO; consolidated.len()];
    for coset_index in 0..lde_factor {
        let coset = trace_holder.get_coset_evaluations(coset_index);
        let dst =
            &mut host_per_coset[coset_index * per_coset_len..(coset_index + 1) * per_coset_len];
        memory_copy_async(dst, coset, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(host_consolidated, host_per_coset);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_full_tree_view_is_contiguous_in_coset_major_order() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = 11u32;
    let log_lde_factor = 2u32;
    let log_rows_per_leaf = 2u32;
    let log_tree_cap_size = 3u32;
    let columns_count = 3usize;
    let lde_factor = 1usize << log_lde_factor;
    let per_coset_tree_len = 1usize << (log_domain_size + 1 - log_rows_per_leaf);

    let (source_host, _) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);
    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CacheFull,
        &context,
    )
    .unwrap();
    holder
        .materialize_and_commit_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let mut concat = vec![Digest::default(); lde_factor * per_coset_tree_len];
    for coset_index in 0..lde_factor {
        let segment_dst =
            &mut concat[coset_index * per_coset_tree_len..(coset_index + 1) * per_coset_tree_len];
        let segment_src: &DeviceSlice<Digest> = holder
            .get_uninit_tree_mut(coset_index)
            .expect("Full mode always has a tree slot");
        memory_copy_async(segment_dst, segment_src, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    // Sanity: cosets produce distinct trees, so segment 0 != segment 1 at index 0.
    assert_ne!(concat[0], concat[per_coset_tree_len]);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_partial_tree_view_is_contiguous_in_coset_major_order() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = 11u32;
    let log_lde_factor = 2u32;
    let log_rows_per_leaf = 2u32;
    let log_tree_cap_size = 3u32;
    let columns_count = 3usize;
    let lde_factor = 1usize << log_lde_factor;
    let partial_log_domain = log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS;
    let per_coset_partial_len = 1usize << (partial_log_domain + 1 - log_rows_per_leaf);

    let (source_host, _) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);
    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CachePartial,
        &context,
    )
    .unwrap();
    holder
        .materialize_and_commit_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let mut concat = vec![Digest::default(); lde_factor * per_coset_partial_len];
    for coset_index in 0..lde_factor {
        let segment_dst = &mut concat
            [coset_index * per_coset_partial_len..(coset_index + 1) * per_coset_partial_len];
        let segment_src: &DeviceSlice<Digest> = holder
            .get_uninit_tree_mut(coset_index)
            .expect("Partial mode always has a tree slot");
        memory_copy_async(segment_dst, segment_src, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    assert_ne!(concat[0], concat[per_coset_partial_len]);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_consolidated_tree_matches_per_coset_views() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = 11u32;
    let log_lde_factor = 2u32;
    let log_rows_per_leaf = 2u32;
    let log_tree_cap_size = 3u32;
    let columns_count = 3usize;
    let lde_factor = 1usize << log_lde_factor;
    let per_coset_tree_len = 1usize << (log_domain_size + 1 - log_rows_per_leaf);

    let (source_host, _) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);
    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CacheFull,
        &context,
    )
    .unwrap();
    holder
        .materialize_and_commit_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let consolidated = holder.get_consolidated_tree().expect("Full mode");
    assert_eq!(consolidated.len(), lde_factor * per_coset_tree_len);

    let mut host_consolidated = vec![Digest::default(); consolidated.len()];
    memory_copy_async(
        &mut host_consolidated,
        consolidated,
        context.get_exec_stream(),
    )
    .unwrap();

    let mut host_per_coset = vec![Digest::default(); consolidated.len()];
    for coset_index in 0..lde_factor {
        let segment_src: &DeviceSlice<Digest> = holder.get_uninit_tree_mut(coset_index).unwrap();
        let dst = &mut host_per_coset
            [coset_index * per_coset_tree_len..(coset_index + 1) * per_coset_tree_len];
        memory_copy_async(dst, segment_src, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(host_consolidated, host_per_coset);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_get_evaluations_returns_coset_zero_subrange() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = PARTIAL_TREE_REDUCTION_LAYERS + 3;
    let log_lde_factor = 2u32;
    let columns_count = 3usize;
    let per_coset_len = columns_count * (1usize << log_domain_size);

    let (source_host, _) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);
    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        0,
        log_lde_factor + 1,
        columns_count,
        TreesCacheMode::CacheNone,
        &context,
    )
    .unwrap();
    holder
        .materialize_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let coset0 = holder.get_evaluations();
    assert_eq!(coset0.len(), per_coset_len);
    let consolidated = holder.get_consolidated_cosets();
    let coset0_via_consolidated = &consolidated[0..per_coset_len];
    let mut a = vec![BF::ZERO; per_coset_len];
    let mut b = vec![BF::ZERO; per_coset_len];
    memory_copy_async(&mut a, coset0, context.get_exec_stream()).unwrap();
    memory_copy_async(&mut b, coset0_via_consolidated, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(a, b);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_consolidated_partial_tree_matches_per_coset_views() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = 11u32;
    let log_lde_factor = 2u32;
    let log_rows_per_leaf = 2u32;
    let log_tree_cap_size = 3u32;
    let columns_count = 3usize;
    let lde_factor = 1usize << log_lde_factor;
    let partial_log_domain = log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS;
    let per_coset_partial_len = 1usize << (partial_log_domain + 1 - log_rows_per_leaf);

    let (source_host, _) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);
    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CachePartial,
        &context,
    )
    .unwrap();
    holder
        .materialize_and_commit_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let consolidated = holder.get_consolidated_tree().expect("Partial mode");
    assert_eq!(consolidated.len(), lde_factor * per_coset_partial_len);

    let mut host_consolidated = vec![Digest::default(); consolidated.len()];
    memory_copy_async(
        &mut host_consolidated,
        consolidated,
        context.get_exec_stream(),
    )
    .unwrap();

    let mut host_per_coset = vec![Digest::default(); consolidated.len()];
    for coset_index in 0..lde_factor {
        let segment_src: &DeviceSlice<Digest> = holder.get_uninit_tree_mut(coset_index).unwrap();
        let dst = &mut host_per_coset
            [coset_index * per_coset_partial_len..(coset_index + 1) * per_coset_partial_len];
        memory_copy_async(dst, segment_src, context.get_exec_stream()).unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(host_consolidated, host_per_coset);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_materialization_matches_cpu_for_single_row_leafs() {
    assert_trace_holder_materialization_and_caps_match_cpu(0);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_materialization_matches_stage1_caps_for_grouped_leafs() {
    assert_trace_holder_materialization_and_caps_match_cpu(2);
}

#[test]
#[cfg(not(no_cuda))]
fn trace_holder_queries_match_across_tree_cache_modes() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = 11u32;
    let log_lde_factor = 2u32;
    let log_rows_per_leaf = 2u32;
    let log_tree_cap_size = 3u32;
    let domain_size = 1usize << log_domain_size;
    let columns_count = 3usize;
    let rows_per_leaf = 1usize << log_rows_per_leaf;
    let (source_host, cpu_cosets) =
        make_source_host_and_cpu_cosets(log_domain_size, log_lde_factor, columns_count, &worker);

    let mut source_device = context
        .alloc(source_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut source_device, &source_host, context.get_exec_stream()).unwrap();

    let mut full_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CacheFull,
        &context,
    )
    .unwrap();
    full_holder
        .materialize_and_commit_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let mut partial_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CachePartial,
        &context,
    )
    .unwrap();
    partial_holder
        .materialize_and_commit_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let mut none_holder = TraceHolder::<BF>::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        columns_count,
        TreesCacheMode::CacheNone,
        &context,
    )
    .unwrap();
    none_holder
        .materialize_and_commit_from_hypercube_evals(&source_device, &context)
        .unwrap();

    let cosets_count = 1usize << log_lde_factor;
    let leaves_per_coset = domain_size >> log_rows_per_leaf;
    let full_tree_stride = leaves_per_coset * 2;
    let partial_tree_stride = full_tree_stride >> PARTIAL_TREE_REDUCTION_LAYERS;
    let cap_per_coset = (1usize << log_tree_cap_size) / cosets_count;
    let initialized_partial_len = partial_tree_stride - cap_per_coset;
    let full_tree = full_holder.get_consolidated_tree().unwrap();
    let partial_tree = partial_holder.get_consolidated_tree().unwrap();
    let mut full_tree_host = vec![Digest::default(); full_tree.len()];
    let mut partial_tree_host = vec![Digest::default(); partial_tree.len()];
    memory_copy_async(&mut full_tree_host, full_tree, context.get_exec_stream()).unwrap();
    memory_copy_async(
        &mut partial_tree_host,
        partial_tree,
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    for coset in 0..cosets_count {
        let full_start = coset * full_tree_stride + full_tree_stride - partial_tree_stride;
        let partial_start = coset * partial_tree_stride;
        assert_eq!(
            &partial_tree_host[partial_start..partial_start + initialized_partial_len],
            &full_tree_host[full_start..full_start + initialized_partial_len],
        );
    }

    let query_indexes = vec![0u32, 1, 7, 13, 42];
    let mut indexes_device = context
        .alloc(query_indexes.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(
        &mut indexes_device,
        &query_indexes,
        context.get_exec_stream(),
    )
    .unwrap();

    let full = full_holder
        .get_leafs_and_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    let full_leafs_only = full_holder
        .get_query_leafs(1, &indexes_device, &context)
        .unwrap();
    let full_paths_only = full_holder
        .get_query_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    let partial = partial_holder
        .get_leafs_and_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    let partial_leafs_only = partial_holder
        .get_query_leafs(1, &indexes_device, &context)
        .unwrap();
    let partial_paths_only = partial_holder
        .get_query_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    let none = none_holder
        .get_leafs_and_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    let none_leafs_only = none_holder
        .get_query_leafs(1, &indexes_device, &context)
        .unwrap();
    let none_paths_only = none_holder
        .get_query_merkle_paths(1, &indexes_device, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let full_leafs = unsafe { full.leafs.get_accessor().get().to_vec() };
    let partial_leafs = unsafe { partial.leafs.get_accessor().get().to_vec() };
    let none_leafs = unsafe { none.leafs.get_accessor().get().to_vec() };
    assert_eq!(partial_leafs, full_leafs);
    assert_eq!(none_leafs, full_leafs);

    let full_paths = unsafe { full.merkle_paths.get_accessor().get().to_vec() };
    let partial_paths = unsafe { partial.merkle_paths.get_accessor().get().to_vec() };
    let none_paths = unsafe { none.merkle_paths.get_accessor().get().to_vec() };
    assert_eq!(partial_paths, full_paths);
    assert_eq!(none_paths, full_paths);
    assert_eq!(unsafe { full_leafs_only.get_accessor().get() }, unsafe {
        full.leafs.get_accessor().get()
    });
    assert_eq!(unsafe { partial_leafs_only.get_accessor().get() }, unsafe {
        partial.leafs.get_accessor().get()
    });
    assert_eq!(unsafe { none_leafs_only.get_accessor().get() }, unsafe {
        none.leafs.get_accessor().get()
    });
    assert_eq!(unsafe { full_paths_only.get_accessor().get() }, unsafe {
        full.merkle_paths.get_accessor().get()
    });
    assert_eq!(unsafe { partial_paths_only.get_accessor().get() }, unsafe {
        partial.merkle_paths.get_accessor().get()
    });
    assert_eq!(unsafe { none_paths_only.get_accessor().get() }, unsafe {
        none.merkle_paths.get_accessor().get()
    });

    let stage1_caps = full_holder
        .read_per_coset_caps_synchronously(&context)
        .unwrap();
    let cpu_caps = stage1_caps_from_cpu_cosets(
        &cpu_cosets,
        domain_size,
        columns_count,
        rows_per_leaf,
        1 << log_tree_cap_size,
        log_lde_factor,
        &worker,
    );
    assert_eq!(stage1_caps, cpu_caps);

    let path_len =
        (log_domain_size - log_rows_per_leaf - (log_tree_cap_size - log_lde_factor)) as usize;
    for (query_slot, &leaf_index) in query_indexes.iter().enumerate() {
        let leaf_words =
            extract_query_leaf_words(&full_leafs, query_slot, query_indexes.len(), rows_per_leaf);
        let merkle_path = (0..path_len)
            .map(|layer| full_paths[query_slot + layer * query_indexes.len()])
            .collect_vec();
        verify_query_against_stage1_caps(
            &leaf_words,
            &merkle_path,
            leaf_index as usize,
            1,
            &stage1_caps,
            log_lde_factor,
        );
    }
}

const PHYSICAL_TREE_SHAPES: [(u32, u32); 6] = [(4, 1), (6, 1), (10, 1), (10, 5), (12, 5), (12, 1)];

fn deterministic_values(len: usize) -> Vec<BF> {
    let mut state = 0x1234_5678_9abc_def0u64;
    (0..len)
        .map(|_| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            BF::from_raw_u32(((state >> 33) as u32) % BF::ORDER)
        })
        .collect_vec()
}

/// Permutes every column of every coset slab from natural row order into the
/// bitreversed row order the LSB commit path consumes.
fn bitreverse_coset_columns(
    values: &[BF],
    cosets_count: usize,
    columns_count: usize,
    log_domain_size: u32,
) -> Vec<BF> {
    let rows_count = 1usize << log_domain_size;
    let coset_stride = columns_count * rows_count;
    let mut result = vec![BF::ZERO; values.len()];
    for coset in 0..cosets_count {
        for column in 0..columns_count {
            let base = coset * coset_stride + column * rows_count;
            for physical in 0..rows_count {
                result[base + physical] =
                    values[base + super::bitreverse_index(physical, log_domain_size)];
            }
        }
    }
    result
}

/// Host blake2s over LOGICAL leaf `leaf`: slot `s` of column `c` reads natural
/// row `leaf + rev_b(s) * leaves_count`, absorbed column-major / slot-fast.
fn host_logical_leaf_digest(
    values: &[BF],
    coset_base: usize,
    rows_count: usize,
    columns_count: usize,
    leaves_count: usize,
    log_rows_per_leaf: u32,
    leaf: usize,
) -> Digest {
    let mut words = Vec::with_capacity(columns_count << log_rows_per_leaf);
    for column in 0..columns_count {
        for slot in 0..1usize << log_rows_per_leaf {
            let row = leaf + super::bitreverse_index(slot, log_rows_per_leaf) * leaves_count;
            words.push(values[coset_base + column * rows_count + row].0);
        }
    }
    hash_leaf_words(&words)
}

fn gather_caps_synchronously(
    tree: &RawDeviceAllocation<Digest>,
    per_coset_tree_stride: usize,
    log_lde_factor: u32,
    log_subtree_cap_size: u32,
    stream: &CudaStream,
) -> Vec<u32> {
    let per_coset_cap_size = 1usize << log_subtree_cap_size;
    let cap_words_per_coset = per_coset_cap_size * BLAKE2S_DIGEST_SIZE_U32_WORDS;
    let cap_offset_words =
        (per_coset_tree_stride - (per_coset_cap_size << 1)) * BLAKE2S_DIGEST_SIZE_U32_WORDS;
    let total_words = cap_words_per_coset << log_lde_factor;
    let mut dst = RawDeviceAllocation::<u32>::alloc(total_words).unwrap();
    // SAFETY: `cap_offset_words` stays inside the first per-coset slab.
    let base = unsafe { (tree.as_ptr() as *const u32).add(cap_offset_words) };
    gather_tree_caps_inline(
        base,
        cap_words_per_coset as u32,
        (per_coset_tree_stride * BLAKE2S_DIGEST_SIZE_U32_WORDS) as u32,
        log_lde_factor,
        &mut dst,
        stream,
    )
    .unwrap();
    let mut host = vec![0u32; total_words];
    memory_copy_async(&mut host, &dst, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

#[test]
#[cfg(not(no_cuda))]
fn full_tree_from_physical_leaves_matches_natural_path() {
    let stream = CudaStream::default();
    let log_subtree_cap_size = 1u32;
    for (log_domain_size, log_rows_per_leaf) in PHYSICAL_TREE_SHAPES {
        for log_lde_factor in [0u32, 1u32] {
            for columns_count in [1usize, 3usize] {
                let log_tree_cap_size = log_lde_factor + log_subtree_cap_size;
                let cosets_in_tile = 1usize << log_lde_factor;
                let rows_count = 1usize << log_domain_size;
                let leaves_count = rows_count >> log_rows_per_leaf;
                let per_coset_evals_stride = columns_count * rows_count;
                let per_coset_tree_stride = leaves_count << 1;
                let trees_len = per_coset_tree_stride * cosets_in_tile;
                let label = format!(
                    "n={log_domain_size} b={log_rows_per_leaf} cosets={cosets_in_tile} \
                     cols={columns_count}"
                );

                let natural = deterministic_values(per_coset_evals_stride * cosets_in_tile);
                let physical = bitreverse_coset_columns(
                    &natural,
                    cosets_in_tile,
                    columns_count,
                    log_domain_size,
                );

                let mut natural_device = RawDeviceAllocation::alloc(natural.len()).unwrap();
                let mut physical_device = RawDeviceAllocation::alloc(physical.len()).unwrap();
                memory_copy_async(&mut natural_device, &natural, &stream).unwrap();
                memory_copy_async(&mut physical_device, &physical, &stream).unwrap();

                // Sentinel fill: any digest neither path writes must stay
                // identical in both backings, so an out-of-region write in
                // either path breaks the whole-backing comparison below.
                let sentinel = vec![[0xdead_beefu32; 8]; trees_len];
                let mut old_tree = RawDeviceAllocation::<Digest>::alloc(trees_len).unwrap();
                let mut new_tree = RawDeviceAllocation::<Digest>::alloc(trees_len).unwrap();
                memory_copy_async(&mut old_tree, &sentinel, &stream).unwrap();
                memory_copy_async(&mut new_tree, &sentinel, &stream).unwrap();

                commit_trace_multi_coset(
                    &natural_device,
                    &mut old_tree,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    cosets_in_tile,
                    &stream,
                )
                .unwrap();
                build_full_trees_from_physical(
                    &physical_device,
                    &mut new_tree,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    cosets_in_tile,
                    &stream,
                )
                .unwrap();

                let mut old_host = vec![Digest::default(); trees_len];
                let mut new_host = vec![Digest::default(); trees_len];
                memory_copy_async(&mut old_host, &old_tree, &stream).unwrap();
                memory_copy_async(&mut new_host, &new_tree, &stream).unwrap();
                stream.synchronize().unwrap();

                for coset in 0..cosets_in_tile {
                    let start = coset * per_coset_tree_stride;
                    for digest in 0..per_coset_tree_stride {
                        assert_eq!(
                            new_host[start + digest],
                            old_host[start + digest],
                            "{label}: coset {coset} tree digest {digest}",
                        );
                    }
                }

                let old_caps = gather_caps_synchronously(
                    &old_tree,
                    per_coset_tree_stride,
                    log_lde_factor,
                    log_subtree_cap_size,
                    &stream,
                );
                let new_caps = gather_caps_synchronously(
                    &new_tree,
                    per_coset_tree_stride,
                    log_lde_factor,
                    log_subtree_cap_size,
                    &stream,
                );
                assert_eq!(new_caps, old_caps, "{label}: unified cap");

                for coset in 0..cosets_in_tile {
                    for leaf in 0..leaves_count {
                        let expected = host_logical_leaf_digest(
                            &natural,
                            coset * per_coset_evals_stride,
                            rows_count,
                            columns_count,
                            leaves_count,
                            log_rows_per_leaf,
                            leaf,
                        );
                        assert_eq!(
                            new_host[coset * per_coset_tree_stride + leaf],
                            expected,
                            "{label}: host oracle coset {coset} logical leaf {leaf}",
                        );
                    }
                }
            }
        }
    }
}

const PHYSICAL_PARTIAL_TREE_SHAPES: [(u32, u32); 2] = [(14, 1), (14, 5)];

#[test]
#[cfg(not(no_cuda))]
fn partial_tree_from_physical_leaves_matches_natural_path() {
    let stream = CudaStream::default();
    let log_subtree_cap_size = 1u32;
    for (log_domain_size, log_rows_per_leaf) in PHYSICAL_PARTIAL_TREE_SHAPES {
        for log_lde_factor in [0u32, 1u32] {
            for columns_count in [1usize, 3usize] {
                let log_tree_cap_size = log_lde_factor + log_subtree_cap_size;
                let cosets_in_tile = 1usize << log_lde_factor;
                let rows_count = 1usize << log_domain_size;
                let leaves_count = rows_count >> log_rows_per_leaf;
                let per_coset_evals_stride = columns_count * rows_count;
                let per_coset_tree_stride = (leaves_count << 1) >> PARTIAL_TREE_REDUCTION_LAYERS;
                let trees_len = per_coset_tree_stride * cosets_in_tile;
                let label = format!(
                    "n={log_domain_size} b={log_rows_per_leaf} cosets={cosets_in_tile} \
                     cols={columns_count}"
                );

                let natural = deterministic_values(per_coset_evals_stride * cosets_in_tile);
                let physical = bitreverse_coset_columns(
                    &natural,
                    cosets_in_tile,
                    columns_count,
                    log_domain_size,
                );

                let mut natural_device = RawDeviceAllocation::alloc(natural.len()).unwrap();
                let mut physical_device = RawDeviceAllocation::alloc(physical.len()).unwrap();
                memory_copy_async(&mut natural_device, &natural, &stream).unwrap();
                memory_copy_async(&mut physical_device, &physical, &stream).unwrap();

                let sentinel = vec![[0xdead_beefu32; 8]; trees_len];
                let mut old_tree = RawDeviceAllocation::<Digest>::alloc(trees_len).unwrap();
                let mut new_tree = RawDeviceAllocation::<Digest>::alloc(trees_len).unwrap();
                memory_copy_async(&mut old_tree, &sentinel, &stream).unwrap();
                memory_copy_async(&mut new_tree, &sentinel, &stream).unwrap();

                commit_trace_with_partial_tree_multi_coset(
                    &natural_device,
                    &mut old_tree,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    cosets_in_tile,
                    &stream,
                )
                .unwrap();
                let mut staging =
                    RawDeviceAllocation::<Digest>::alloc(leaves_count * cosets_in_tile).unwrap();
                build_partial_trees_from_physical(
                    &physical_device,
                    &mut new_tree,
                    log_domain_size,
                    log_lde_factor,
                    log_rows_per_leaf,
                    log_tree_cap_size,
                    columns_count,
                    cosets_in_tile,
                    &mut staging,
                    &stream,
                )
                .unwrap();

                let mut old_host = vec![Digest::default(); trees_len];
                let mut new_host = vec![Digest::default(); trees_len];
                memory_copy_async(&mut old_host, &old_tree, &stream).unwrap();
                memory_copy_async(&mut new_host, &new_tree, &stream).unwrap();
                stream.synchronize().unwrap();
                assert_eq!(new_host, old_host, "{label}: partial tree backing");

                let old_caps = gather_caps_synchronously(
                    &old_tree,
                    per_coset_tree_stride,
                    log_lde_factor,
                    log_subtree_cap_size,
                    &stream,
                );
                let new_caps = gather_caps_synchronously(
                    &new_tree,
                    per_coset_tree_stride,
                    log_lde_factor,
                    log_subtree_cap_size,
                    &stream,
                );
                assert_eq!(new_caps, old_caps, "{label}: unified cap");
            }
        }
    }
}
