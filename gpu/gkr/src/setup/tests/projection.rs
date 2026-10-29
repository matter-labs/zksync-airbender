use super::*;
use gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS;

fn read_tree(tree: &DeviceSlice<Digest>, context: &ProverContext) -> Vec<Digest> {
    let mut host = vec![[0; 8]; tree.len()];
    memory_copy_async(&mut host, tree, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

#[test]
fn cpu_setup_projection_offsets_and_direction() {
    for (source_depth, target_depth, source_len, target_len, offset) in [
        (5, 5, 128, 128, 0),
        (5, 10, 128, 4, 124),
        (5, 10, (1 << 20) - 1, (1 << 15) - 1, 1_015_808),
        (4, 4, 1, 1, 0),
    ] {
        assert_eq!(
            partial_tree_projection_start(
                "setup projection",
                source_depth,
                target_depth,
                source_len,
                target_len,
            ),
            offset
        );
    }
    for name in ["GpuGKRSetupTransfer", "PackedSetupSource"] {
        for (source_depth, target_depth, source_len, target_len, message) in [
            (
                6,
                5,
                64,
                32,
                "target partial-tree depth must be >= source depth",
            ),
            (5, 6, 32, 64, "target partial tree must fit the source tree"),
        ] {
            let panic = std::panic::catch_unwind(|| {
                partial_tree_projection_start(
                    name,
                    source_depth,
                    target_depth,
                    source_len,
                    target_len,
                )
            })
            .unwrap_err();
            let message_actual = panic.downcast_ref::<String>().unwrap();
            assert!(message_actual.contains(name) && message_actual.contains(message));
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
fn setup_projection_matches_fresh_trees_and_lazy_openings() {
    let context = make_test_context(256, 64);
    for (log_rows, log_rows_per_leaf, log_lde, log_cap) in [(12, 1, 2, 3), (8, 1, 1, 2)] {
        let rows = 1usize << log_rows;
        let setup = make_test_cpu_setup(rows, 3, rows);
        let host = Arc::new(
            GpuGKRSetupHost::precompute_from_cpu_setup(
                &setup,
                log_lde,
                log_rows_per_leaf,
                log_cap,
                &context,
            )
            .unwrap(),
        );
        assert_eq!(
            host.partial_tree_reduction_layers,
            PARTIAL_TREE_REDUCTION_LAYERS
        );
        let source_len = host.partial_trees[0].len();
        for requested in 5..=10 {
            let mut projected =
                GpuGKRSetupTransfer::new(Arc::clone(&host), requested, &context).unwrap();
            let transfer = gpu_prover_context::transfer::single_shot_h2d(
                |t| projected.schedule_transfer(t, &context),
                &context,
            )
            .unwrap();
            transfer.ensure_transferred(&context).unwrap();
            assert!(!projected.trace_holder.are_cosets_materialized());
            let target = requested.min(log_rows - log_rows_per_leaf - (log_cap - log_lde));
            assert_eq!(
                projected.trace_holder.partial_tree_reduction_layers(),
                target
            );
            let mut fresh = TraceHolder::<BF>::new(
                log_rows,
                log_lde,
                log_rows_per_leaf,
                log_cap,
                3,
                TreesCacheMode::CachePartial,
                requested,
                &context,
            )
            .unwrap();
            memory_copy_async(
                fresh.get_uninit_hypercube_evals_mut(),
                &host.raw_hypercube_evals[..],
                context.get_exec_stream(),
            )
            .unwrap();
            fresh.ensure_cosets_materialized(&context).unwrap();
            fresh.commit_all(&context).unwrap();
            let actual = read_tree(
                projected.trace_holder.get_consolidated_tree().unwrap(),
                &context,
            );
            let expected = read_tree(fresh.get_consolidated_tree().unwrap(), &context);
            let stride = 1usize << (log_rows + 1 - log_rows_per_leaf - target);
            assert_eq!(actual.len(), stride << log_lde);
            let initialized = stride - (1 << (log_cap - log_lde));
            for coset in 0..1usize << log_lde {
                let range = coset * stride..coset * stride + initialized;
                assert_eq!(
                    actual[range.clone()],
                    expected[range],
                    "rows={log_rows} requested={requested} coset={coset}"
                );
                assert_eq!(
                    &actual[coset * stride..coset * stride + initialized],
                    &host.partial_trees[coset]
                        [source_len - stride..source_len - stride + initialized]
                );
            }
            assert_eq!(
                read_tree(projected.unified_device_cap(), &context),
                read_tree(fresh.unified_device_cap(), &context)
            );
            let leaves = 1u32 << (log_rows - log_rows_per_leaf);
            let subtree = 1u32 << target;
            let mut queries = vec![0, 1, leaves - 1, 0];
            for boundary in (subtree..leaves).step_by(subtree as usize) {
                queries.extend([boundary - 1, boundary]);
            }
            let mut indexes = context
                .alloc(queries.len(), AllocationPlacement::BestFit)
                .unwrap();
            memory_copy_async(&mut indexes, &queries, context.get_exec_stream()).unwrap();
            for coset in 0..1usize << log_lde {
                let actual = projected
                    .trace_holder
                    .get_leafs_and_merkle_paths(coset, &indexes, &context)
                    .unwrap();
                let expected = fresh
                    .get_leafs_and_merkle_paths(coset, &indexes, &context)
                    .unwrap();
                context.get_exec_stream().synchronize().unwrap();
                assert_eq!(unsafe { actual.leafs.get_accessor().get() }, unsafe {
                    expected.leafs.get_accessor().get()
                });
                assert_eq!(
                    unsafe { actual.merkle_paths.get_accessor().get() },
                    unsafe { expected.merkle_paths.get_accessor().get() }
                );
            }
            assert_eq!(host.partial_tree_reduction_layers, 5);
            assert_eq!(host.partial_trees[0].len(), source_len);
        }
    }
}
