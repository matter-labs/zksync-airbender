use super::*;
use field::Field;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::transfer::single_shot_h2d;
use gpu_prover_context::ProverContextConfig;
use gpu_trace::trace::packed::opening_path_len;

fn read_back<T: Copy>(device: &DeviceSlice<T>, initial: T, context: &ProverContext) -> Vec<T> {
    let mut host = vec![initial; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn open(
    oracle: &PackedCosetRecomputeOracle<PR>,
    queries: &DeviceSlice<u32>,
    context: &ProverContext,
) -> (Vec<PR>, Vec<Digest>, Vec<u32>) {
    let cfg = oracle.config().unwrap();
    let leaf_len = oracle.packed_columns() << cfg.log_values_per_leaf;
    let depth = opening_path_len(oracle.log_packed(), &cfg);
    let mut leaves = context
        .alloc(queries.len() * leaf_len, AllocationPlacement::BestFit)
        .unwrap();
    let mut paths = context
        .alloc(queries.len() * depth, AllocationPlacement::BestFit)
        .unwrap();
    let mut indexes = context
        .alloc(queries.len(), AllocationPlacement::BestFit)
        .unwrap();
    let plan = gpu_trace::trace::packed::CosetQueryPlan::new(queries, cfg.log_lde_factor, context)
        .unwrap();
    oracle
        .open_queries(
            &plan,
            queries,
            &mut leaves,
            &mut paths,
            &mut indexes,
            context,
        )
        .unwrap();
    (
        read_back(&leaves, PR::ZERO, context),
        read_back(&paths, [0; 8], context),
        read_back(&indexes, 0, context),
    )
}

#[test]
#[cfg(not(no_cuda))]
fn setup_projection_matches_fresh_packed_trees_and_openings() {
    let context = ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(256),
        host_allocator_blocks_count: 64,
        proth120_ntt_log_max_domain: Some(
            gpu_prover_context::ProverContext::PROTH120_NTT_LOG_MAX_DOMAIN,
        ),
        ..Default::default()
    })
    .unwrap();
    for (log_rows, pack_log2, log_v, cap_log) in [(15, 3, 1, 3)] {
        let columns_count = 10;
        let log_leaves = log_rows + pack_log2 - log_v;
        let source_cfg = PackedCommitConfig {
            log_lde_factor: 4,
            log_values_per_leaf: log_v,
            cap_log,
            skip_bottom: PARTIAL_TREE_REDUCTION_LAYERS.min(log_leaves),
        };
        let setup = CpuGKRSetup {
            hypercube_evals: (0..columns_count)
                .map(|column| {
                    let values: Vec<PR> = (0..1usize << log_rows)
                        .map(|row| {
                            PR::from_u128_with_reduction(
                                (((column + 1) as u128) << 80)
                                    + (row * row + 17 * row + column) as u128,
                            )
                        })
                        .collect();
                    Arc::new(prover::allocation_pool::AllocationType::from(
                        values.into_boxed_slice(),
                    ))
                })
                .collect(),
        };
        let host =
            Arc::new(L1WrapSetupHost::precompute(&setup, pack_log2, source_cfg, &context).unwrap());
        let source_len = retained_len(log_leaves, source_cfg.skip_bottom);
        for requested in [10] {
            let mut projected =
                PackedSetupSource::new(Arc::clone(&host), requested, &context).unwrap();
            let transfer =
                single_shot_h2d(|t| projected.schedule_transfer(t, &context), &context).unwrap();
            transfer.ensure_transferred(&context).unwrap();
            let cfg = projected.oracle.config().unwrap();
            assert!(cfg.same_protocol_geometry(&source_cfg));
            assert_eq!(cfg.skip_bottom, requested.min(log_leaves));
            let mut raw = TraceHolder::new_without_cosets(
                log_rows,
                cfg.log_lde_factor,
                log_v,
                cap_log,
                columns_count,
                TreesCacheMode::CacheNone,
                requested,
                &context,
            )
            .unwrap();
            memory_copy_async(
                raw.get_uninit_hypercube_evals_mut(),
                &host.raw_hypercube_evals[..],
                context.get_exec_stream(),
            )
            .unwrap();
            let mut fresh =
                PackedCosetRecomputeOracle::pack_from_columns(raw, pack_log2, &context).unwrap();
            fresh.commit(&cfg, &context).unwrap();
            let actual = read_back(projected.oracle.uninit_retained_mut(), [0; 8], &context);
            let expected = read_back(fresh.uninit_retained_mut(), [0; 8], &context);
            assert_eq!(actual, expected, "h={log_leaves} requested={requested}");
            let target_len = retained_len(log_leaves, cfg.skip_bottom);
            for coset in 0..16 {
                assert_eq!(
                    &actual[coset * target_len..(coset + 1) * target_len],
                    &host.retained
                        [coset * source_len + source_len - target_len..(coset + 1) * source_len],
                );
            }
            assert_eq!(
                read_back(projected.oracle.uninit_roots_mut(), [0; 8], &context),
                read_back(fresh.uninit_roots_mut(), [0; 8], &context)
            );
            assert_eq!(
                read_back(projected.oracle.uninit_top_nodes_mut(), [0; 8], &context),
                read_back(fresh.uninit_top_nodes_mut(), [0; 8], &context)
            );
            assert_eq!(
                read_back(projected.oracle.cap_digests(), [0; 8], &context),
                read_back(fresh.cap_digests(), [0; 8], &context)
            );
            assert_eq!(
                read_back(projected.oracle.monomials(), PR::ZERO, &context),
                read_back(fresh.monomials(), PR::ZERO, &context)
            );
            assert_eq!(
                read_back(
                    projected.oracle.raw().get_hypercube_evals(),
                    PR::ZERO,
                    &context
                ),
                &host.raw_hypercube_evals[..]
            );
            let leaves = 1u32 << log_leaves;
            let subtree = 1u32 << cfg.skip_bottom;
            let queries: Vec<u32> = [0, subtree - 1, subtree, leaves - 1]
                .into_iter()
                .flat_map(|leaf| {
                    [15, 1, 0]
                        .into_iter()
                        .map(move |coset| (leaf << cfg.log_lde_factor) | coset)
                })
                .collect();
            let mut device_queries = context
                .alloc(queries.len(), AllocationPlacement::BestFit)
                .unwrap();
            memory_copy_async(&mut device_queries, &queries, context.get_exec_stream()).unwrap();
            assert_eq!(
                open(&projected.oracle, &device_queries, &context),
                open(&fresh, &device_queries, &context),
                "h={log_leaves} requested={requested}"
            );
            assert_eq!(host.cfg, source_cfg);
            assert_eq!(host.retained.len(), source_len * 16);
        }
    }
}
