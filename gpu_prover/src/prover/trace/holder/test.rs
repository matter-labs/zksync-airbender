
use std::alloc::Global;

use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use era_cudart::memory::memory_copy_async;
use field::{Field, PrimeField};
use itertools::Itertools;
use prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals;
use prover::merkle_trees::blake2s_for_everything_tree::Blake2sU32MerkleTreeWithCap;
use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, MerkleTreeCapVarLength};
use serial_test::serial;
use worker::Worker;

use super::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::prover::test_utils::make_test_context;

impl<T> TraceHolder<T> {
    /// Reads the unified device cap back to host and returns it as a single
    /// `MerkleTreeCapVarLength`. Performs an exec-stream synchronize, so it is
    /// only meant for tests / one-shot helpers, not for the `prove()` hot path.
    pub(crate) fn read_full_cap_synchronously(
        &self,
        context: &ProverContext,
    ) -> CudaResult<MerkleTreeCapVarLength> {
        let device_cap = self.unified_device_cap();
        let cap_size = device_cap.len();
        debug_assert_eq!(cap_size, 1usize << self.log_tree_cap_size);
        let stream = context.get_exec_stream();
        let mut host = vec![Digest::default(); cap_size];
        memory_copy_async(host.as_mut_slice(), device_cap, stream)?;
        stream.synchronize()?;
        Ok(MerkleTreeCapVarLength { cap: host })
    }

    /// Reads the unified device cap back to host and chops it into the
    /// per-coset `MerkleTreeCapVarLength` shape. Used by tests that compare
    /// against CPU caps produced per-coset. Performs a host synchronize.
    pub(crate) fn read_per_coset_caps_synchronously(
        &self,
        context: &ProverContext,
    ) -> CudaResult<Vec<MerkleTreeCapVarLength>> {
        let lde_factor = 1usize << self.log_lde_factor;
        let full = self.read_full_cap_synchronously(context)?.cap;
        debug_assert_eq!(full.len() % lde_factor, 0);
        let per_coset = full.len() / lde_factor;
        Ok((0..lde_factor)
            .map(|stage1_pos| MerkleTreeCapVarLength {
                cap: full[stage1_pos * per_coset..(stage1_pos + 1) * per_coset].to_vec(),
            })
            .collect_vec())
    }
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
        >>::construct_from_cosets::<BF, Global>(
            &source_refs,
            rows_per_leaf,
            total_cap_size,
            true,
            true,
            false,
            worker,
        );
    let subcap_size = total_cap_size >> log_lde_factor;
    <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(&tree)
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
        CosetsHolder::Full(cosets) => {
            for (coset_idx, coset) in cosets.iter().enumerate() {
                let mut gpu = vec![BF::ZERO; coset.len()];
                memory_copy_async(&mut gpu, coset, context.get_exec_stream()).unwrap();
                context.get_exec_stream().synchronize().unwrap();
                assert_eq!(gpu, cpu_cosets[coset_idx], "coset {}", coset_idx);
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
#[serial]
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
        CosetsHolder::Full(cosets) => {
            for (coset_idx, coset) in cosets.iter().enumerate() {
                let mut gpu = vec![BF::ZERO; coset.len()];
                memory_copy_async(&mut gpu, coset, context.get_exec_stream()).unwrap();
                context.get_exec_stream().synchronize().unwrap();
                assert_eq!(gpu, cpu_cosets[coset_idx], "coset {}", coset_idx);
            }
        }
        CosetsHolder::None(_) => panic!("expected Full cosets in test"),
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn trace_holder_materialization_matches_cpu_for_single_row_leafs() {
    assert_trace_holder_materialization_and_caps_match_cpu(0);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn trace_holder_materialization_matches_stage1_caps_for_grouped_leafs() {
    assert_trace_holder_materialization_and_caps_match_cpu(2);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn trace_holder_queries_match_across_tree_cache_modes() {
    let worker = Worker::new();
    let context = make_test_context(256, 32);
    let log_domain_size = 9u32;
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
