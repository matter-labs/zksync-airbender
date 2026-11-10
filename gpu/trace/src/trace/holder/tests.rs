use era_cudart::memory::memory_copy_async;

use super::*;
use crate::upstream::{Field, PrimeField};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContextConfig;

// Local test-context builder for the `gpu_trace` suites. Mirrors the apex
// `prover::test_utils::make_test_context` minus its GKR `configure_kernel_
// attributes()` call, which only sets shared-memory carveout on the
// `ab_gkr_main_round*` flat kernels and is unreachable from this crate.
const TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

fn make_test_context(
    device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
) -> ProverContext {
    let default_block_log_size = ProverContextConfig::default().allocator_block_log_size;
    let arena_bytes = device_allocation_blocks_count << default_block_log_size;
    let test_blocks_count = arena_bytes >> TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    let mut config = ProverContextConfig {
        allocator_block_log_size: TEST_DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
        device_allocation_blocks_count: Some(test_blocks_count),
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

#[test]
fn padded_raw_backing_preserves_prefix_and_zeros_recycled_tail_before_transfer() {
    use gpu_prover_context::transfer::Transfer;

    let context = make_test_context(64, 16);
    let baseline = context.get_used_mem_current();
    let rows = 1 << 8;
    let mut dirty = context
        .alloc::<u32>(8 * rows, AllocationPlacement::Bottom)
        .unwrap();
    let recycled_ptr = dirty.as_ptr();
    memory_set_async(
        // SAFETY: this exclusive allocation consists entirely of initialized-size u32 storage.
        unsafe { dirty.transmute_mut::<u8>() },
        0xff,
        context.get_exec_stream(),
    )
    .unwrap();
    drop(dirty);
    let mut holder = TraceHolder::<u32>::new_without_cosets_padded(
        8,
        1,
        1,
        3,
        5,
        2,
        TreesCacheMode::CacheNone,
        crate::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        &context,
    )
    .unwrap();
    assert_eq!(holder.padded_hypercube_evals().as_ptr(), recycled_ptr);
    assert_eq!(holder.padded_hypercube_evals().len(), 8 * rows);
    assert_eq!(holder.get_hypercube_evals().len(), 5 * rows);
    assert_eq!(holder.get_uninit_hypercube_evals_mut().len(), 5 * rows);
    let source: Vec<u32> = (0..5 * rows).map(|i| i as u32 + 1).collect();
    let mut transfer = Transfer::new().unwrap();
    transfer.record_allocated(&context).unwrap();
    transfer.stage(&source, holder.get_uninit_hypercube_evals_mut());
    transfer.record_transferred(&context).unwrap();
    transfer.ensure_transferred(&context).unwrap();
    let mut actual = vec![u32::MAX; 8 * rows];
    memory_copy_async(
        &mut actual,
        holder.padded_hypercube_evals(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(&actual[..5 * rows], source.as_slice());
    assert!(actual[5 * rows..].iter().all(|&value| value == 0));
    drop(transfer);
    drop(holder);
    assert_eq!(context.get_used_mem_current(), baseline);
}

#[test]
fn deep_partial_trees_install_lazily_and_open_like_depth_five() {
    use gpu_hash::blake2s::{
        gather_merkle_paths_partial_for_queries_physical, OraclePartialPathDesc,
    };
    let context = make_test_context(256, 16);
    let stream = context.get_exec_stream();
    let (log_n, log_f, log_rows, log_cap, cols) = (20, 2, 1, 4, 2);
    let source: Vec<_> = (0..cols << log_n)
        .map(|i| BF::from_u32_unchecked(((i * 31) ^ (i >> 7)) as u32))
        .collect();
    let leaves = 1u32 << (log_n - log_rows);
    let query_host: Vec<u32> = (0..1u32 << log_f)
        .flat_map(|c| [0, 1, 1023, 1024, leaves - 1].map(|leaf| (leaf << log_f) | c))
        .collect();
    let mut queries = context
        .alloc(query_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut queries, &query_host, stream).unwrap();
    let leaf_host = [0, 1, 1023, 1024, 4095, 4096, leaves - 1];
    let mut leaf_indexes = context
        .alloc(leaf_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut leaf_indexes, &leaf_host, stream).unwrap();
    let layers = log_n - log_rows - (log_cap - log_f);
    let open = |holder: &mut TraceHolder<BF>, reduction_layers: u32| {
        let mut paths = context
            .alloc::<u32>(
                query_host.len() * layers as usize * 8,
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let desc = OraclePartialPathDesc {
            cosets_ptr: holder.get_consolidated_cosets().as_ptr() as u64,
            partial_tree_ptr: holder.get_consolidated_tree().unwrap().as_ptr() as u64,
            columns_count: cols as u32,
            slab_dst_ptr: paths.as_mut_ptr() as u64,
            ..Default::default()
        };
        gather_merkle_paths_partial_for_queries_physical(
            desc,
            log_f,
            log_rows,
            log_n - log_rows,
            layers,
            reduction_layers,
            &queries,
            stream,
        )
        .unwrap();
        let coset_paths = holder
            .get_query_merkle_paths(1, &leaf_indexes, &context)
            .unwrap();
        let mut host = vec![0u32; paths.len()];
        memory_copy_async(&mut host, &paths, stream).unwrap();
        stream.synchronize().unwrap();
        (host, unsafe { coset_paths.get_accessor().get().to_vec() })
    };
    let mut baseline = TraceHolder::<BF>::new_without_cosets(
        log_n,
        log_f,
        log_rows,
        log_cap,
        cols,
        TreesCacheMode::CacheNone,
        PARTIAL_TREE_REDUCTION_LAYERS,
        &context,
    )
    .unwrap();
    memory_copy_async(baseline.get_uninit_hypercube_evals_mut(), &source, stream).unwrap();
    baseline.prepare_full_opening(&context).unwrap();
    let expected = open(&mut baseline, PARTIAL_TREE_REDUCTION_LAYERS);
    let mut expected_cap = vec![Digest::default(); 1 << log_cap];
    let mut monomial_baseline = TraceHolder::<BF>::new_without_cosets(
        log_n,
        log_f,
        log_rows,
        log_cap,
        cols,
        TreesCacheMode::CacheNone,
        PARTIAL_TREE_REDUCTION_LAYERS,
        &context,
    )
    .unwrap();
    memory_copy_async(
        monomial_baseline.get_uninit_hypercube_evals_mut(),
        &source,
        stream,
    )
    .unwrap();
    monomial_baseline.install_partial_trees(&context).unwrap();
    monomial_baseline
        .commit_with_monomials(None, &context)
        .unwrap();
    memory_copy_async(
        &mut expected_cap,
        monomial_baseline.unified_device_cap(),
        stream,
    )
    .unwrap();
    for reduction_layers in PARTIAL_TREE_REDUCTION_LAYERS + 1..=MAX_PARTIAL_TREE_REDUCTION_LAYERS {
        let mut lazy = TraceHolder::<BF>::new_without_cosets(
            log_n,
            log_f,
            log_rows,
            log_cap,
            cols,
            TreesCacheMode::CacheNone,
            reduction_layers,
            &context,
        )
        .unwrap();
        memory_copy_async(lazy.get_uninit_hypercube_evals_mut(), &source, stream).unwrap();
        lazy.prepare_full_opening(&context).unwrap();
        assert_eq!(lazy.partial_tree_reduction_layers(), reduction_layers);
        assert_eq!(
            lazy.get_consolidated_tree().unwrap().len(),
            (1usize << log_f) << (log_n - log_rows + 1 - reduction_layers)
        );
        let actual = open(&mut lazy, reduction_layers);
        let first_multi = actual.0.iter().zip(&expected.0).position(|(a, b)| a != b);
        let first_rows = actual.1.iter().zip(&expected.1).position(|(a, b)| a != b);
        assert_eq!(
            (first_multi, first_rows),
            (None, None),
            "L={reduction_layers}: lazy (multi word, rows digest)"
        );

        let mut installed = TraceHolder::<BF>::new_without_cosets(
            log_n,
            log_f,
            log_rows,
            log_cap,
            cols,
            TreesCacheMode::CacheNone,
            reduction_layers,
            &context,
        )
        .unwrap();
        memory_copy_async(installed.get_uninit_hypercube_evals_mut(), &source, stream).unwrap();
        installed.install_partial_trees(&context).unwrap();
        installed.commit_with_monomials(None, &context).unwrap();
        let mut cap = vec![Digest::default(); 1 << log_cap];
        memory_copy_async(&mut cap, installed.unified_device_cap(), stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(cap, expected_cap, "L={reduction_layers}: installed cap");
    }
    let clamped = TraceHolder::<BF>::new_without_cosets(
        12,
        log_f,
        log_rows,
        log_cap,
        cols,
        TreesCacheMode::CacheNone,
        MAX_PARTIAL_TREE_REDUCTION_LAYERS,
        &context,
    )
    .unwrap();
    assert_eq!(
        clamped.partial_tree_reduction_layers(),
        12 - log_rows - (log_cap - log_f)
    );
}

fn open_recomputed(
    holder: &mut TraceHolder<BF>,
    queries_host: &[u32],
    context: &ProverContext,
) -> (Vec<BF>, Vec<u32>) {
    let stream = context.get_exec_stream();
    let layers = holder.log_domain_size
        - holder.log_rows_per_leaf
        - (holder.log_tree_cap_size - holder.log_lde_factor);
    let mut queries = context
        .alloc(queries_host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut queries, queries_host, stream).unwrap();
    let leaf_sentinel = vec![
        BF::from_u32_unchecked(42);
        queries_host.len() * (holder.columns_count << holder.log_rows_per_leaf)
    ];
    let path_sentinel = vec![0xdeadbeefu32; queries_host.len() * layers as usize * 8];
    let mut leaves = context
        .alloc::<BF>(leaf_sentinel.len(), AllocationPlacement::BestFit)
        .unwrap();
    let mut paths = context
        .alloc::<u32>(path_sentinel.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut leaves, &leaf_sentinel, stream).unwrap();
    memory_copy_async(&mut paths, &path_sentinel, stream).unwrap();
    holder.defer_materialization_until_queries(OpeningStrategy::PerCoset);
    holder.finish_raw_batching(context).unwrap();
    holder
        .gather_openings_recomputed(&queries, &mut leaves, &mut paths, context)
        .unwrap();
    let mut leaves_host = vec![BF::ZERO; leaves.len()];
    let mut paths_host = vec![0u32; paths.len()];
    memory_copy_async(&mut leaves_host, &leaves, stream).unwrap();
    memory_copy_async(&mut paths_host, &paths, stream).unwrap();
    stream.synchronize().unwrap();
    assert_ne!(leaves_host, leaf_sentinel);
    assert_ne!(paths_host, path_sentinel);
    (leaves_host, paths_host)
}

#[test]
fn persisted_partial_trees_open_like_rebuilt_trees() {
    use crate::trace::memory::schedule_memory_cap_readback;
    use crate::trace::memory_cap::{
        GpuGKRMemoryCapHost, GpuGKRMemoryCapTransfer, PartialTreesGeometry,
    };
    use era_cudart::memory::{CudaHostAllocFlags, HostAllocation};
    use execution_prover_model::allocator::PooledHostBuffer;
    use gpu_core::allocator::host::ConcurrentStaticHostAllocator;
    use gpu_core::primitives::callbacks::Callbacks;
    use gpu_core::primitives::device_tracing::Range;
    use gpu_prover_context::transfer::Transfer;
    use std::sync::Arc;

    let context = make_test_context(256, 128);
    let stream = context.get_exec_stream();
    let log_n = 20;
    let log_f = 4;
    let log_rows = 1;
    let cols = 2;
    let source: Vec<_> = (0..cols << log_n)
        .map(|i| BF::from_u32_unchecked(((i * 29) ^ (i >> 9)) as u32))
        .collect();
    let sentinel: Digest = [0xdeadbeef; 8];
    let last_leaf = (1u32 << (log_n - log_rows)) - 1;
    // Every coset, each queried more than once.
    let every_coset: Vec<u32> = (0..1u32 << log_f)
        .flat_map(|c| [c, (last_leaf << log_f) | c, (137 << log_f) | c, c])
        .collect();
    // No query in coset 1, the first one transformed (fused with the iNTT).
    let without_first: Vec<u32> = every_coset
        .iter()
        .copied()
        .filter(|query| query & ((1 << log_f) - 1) != 1)
        .collect();
    for log_cap in [log_f, log_f + 2] {
        let config = prover::gkr::prover_config::ProverConfig::whir_only(
            log_n as usize,
            prover::gkr::prover_config::WhirSchedule::from_legacy_arrays(
                1 << log_f,
                1 << log_cap,
                0,
                &[1, 5],
                &[1, 1],
                &[2],
                &[0, 0],
            ),
            prover::definitions::SecurityLevel::Sec100,
        );
        let base_geometry = crate::upstream::BaseCommitmentGeometry::from_config(
            &config,
            crate::upstream::BaseColumns {
                memory: cols,
                witness: 0,
                setup: 0,
            },
        );
        for reduction_layers in [PARTIAL_TREE_REDUCTION_LAYERS, 10] {
            let label = format!("cap 2^{log_cap}, depth {reduction_layers}");
            let new_holder = || {
                let mut holder = TraceHolder::<BF>::new_base_without_cosets(
                    base_geometry,
                    crate::upstream::BaseOracleRole::Memory,
                    TreesCacheMode::CacheNone,
                    reduction_layers,
                    &context,
                )
                .unwrap();
                memory_copy_async(holder.get_uninit_hypercube_evals_mut(), &source, stream)
                    .unwrap();
                holder
            };
            // The production commitment sequence of
            // `schedule_memory_commitment_job_with_monomials`, with the tree
            // slots poisoned before the build.
            let mut committed = new_holder();
            committed.install_partial_trees(&context).unwrap();
            let geometry = PartialTreesGeometry::of_holder(&committed);
            let TreesHolder::Partial(slab) = &mut committed.trees else {
                unreachable!()
            };
            memory_copy_async(slab, &vec![sentinel; slab.len()], stream).unwrap();
            committed.commit_with_monomials(None, &context).unwrap();
            committed.retain_after_commitment(WitnessPostCommitStorage::RawAndMonomials);
            let range = Range::new("persisted_partial_trees").unwrap();
            range.start(stream).unwrap();
            let node_count = geometry.cosets_count() * geometry.coset_stride();
            let backing = HostAllocation::alloc(
                node_count * size_of::<Digest>(),
                CudaHostAllocFlags::DEFAULT,
            )
            .unwrap();
            let allocator = ConcurrentStaticHostAllocator::new([backing], 12);
            let buffer = PooledHostBuffer::new(
                Vec::with_capacity_in(node_count, allocator),
                crossbeam_channel::unbounded().0,
            );
            let job = schedule_memory_cap_readback(
                &committed,
                Callbacks::new(),
                None,
                range,
                Some(buffer),
                &context,
            )
            .unwrap();
            let mut slab_host =
                vec![Digest::default(); geometry.cosets_count() * geometry.coset_stride()];
            memory_copy_async(
                &mut slab_host,
                committed.get_consolidated_tree().unwrap(),
                stream,
            )
            .unwrap();
            let (caps, trees, _) = job.finish_with_partial_trees().unwrap();
            stream.synchronize().unwrap();
            drop(committed);
            let trees = trees.expect("the commitment exported its partial trees");
            let live = geometry.coset_live_len();
            assert_eq!(trees.geometry, geometry, "{label}");
            assert_eq!(
                trees.nodes.len(),
                geometry.cosets_count() * geometry.coset_stride(),
                "{label}"
            );
            assert!(!trees.nodes.contains(&sentinel), "{label}: payload");
            for (coset, (device, exported)) in slab_host
                .chunks_exact(geometry.coset_stride())
                .zip(trees.nodes.chunks_exact(geometry.coset_stride()))
                .enumerate()
            {
                assert_eq!(
                    &device[..live],
                    &exported[..live],
                    "{label}: coset {coset} live nodes"
                );
                assert!(
                    device[live..].iter().all(|digest| *digest == sentinel),
                    "{label}: coset {coset} builder wrote past its cap"
                );
            }
            let host = Arc::new(GpuGKRMemoryCapHost::from_per_coset_caps_and_partial_trees(
                &caps,
                base_geometry,
                geometry,
                trees,
            ));
            for queries in [&every_coset, &without_first] {
                let mut imported = new_holder();
                let mut memory = GpuGKRMemoryCapTransfer::new(Arc::clone(&host), &context).unwrap();
                let mut transfer = Transfer::new().unwrap();
                transfer.record_allocated(&context).unwrap();
                memory.stage_transfer(&mut transfer);
                memory
                    .schedule_partial_tree_transfer(&mut transfer, &context)
                    .unwrap();
                transfer.record_transferred(&context).unwrap();
                transfer.ensure_transferred(&context).unwrap();
                let (geometry, device) = memory.take_partial_trees().unwrap();
                imported.install_transferred_partial_trees(geometry, device);
                let imported_openings = open_recomputed(&mut imported, queries, &context);
                let rebuilt_openings = open_recomputed(&mut new_holder(), queries, &context);
                assert!(
                    imported_openings == rebuilt_openings,
                    "{label}, {} queries: imported-tree openings differ from rebuilt",
                    queries.len()
                );
                drop(memory);
                drop(transfer);
            }
        }
    }
}
