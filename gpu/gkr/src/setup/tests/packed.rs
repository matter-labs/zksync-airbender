use super::*;
use gpu_core::primitives::context::UnsafeMutAccessor;
use prover::definitions::SecurityLevel;
use prover::gkr::prover::stages::commitment_utils::commit_trace_part_with_packing;
use prover::gkr::prover::WhirSchedule;
use prover::gkr::prover_config::commitment_geometry::BaseCommitmentGeometry;
use prover::gkr::prover_config::BaseColumns;
use prover::gkr::prover_config::ProverConfig;

#[test]
fn cpu_packed_setup_geometry_rejects_mismatched_sources() {
    let config = ProverConfig::whir_only(
        13,
        WhirSchedule::from_legacy_arrays(2, 16, 0, &[1, 5], &[1, 1], &[2], &[0, 0]),
        SecurityLevel::Sec100,
    );
    let geometry = BaseCommitmentGeometry::from_config(
        &config,
        BaseColumns {
            memory: 0,
            witness: 0,
            setup: 3,
        },
    )
    .unwrap();
    let setup = make_test_cpu_setup(1 << 13, 3, 8);
    GpuGKRSetupHost::validate_base_geometry(&setup, &geometry);
    for setup in [
        make_test_cpu_setup(1 << 13, 2, 8),
        make_test_cpu_setup(1 << 12, 3, 8),
        make_test_cpu_setup(1 << 13, 0, 0),
    ] {
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            GpuGKRSetupHost::validate_base_geometry(&setup, &geometry)
        }))
        .is_err());
    }
}

#[test]
fn legacy_setup_host_rejects_virtual_before_device_holder() {
    let context = make_test_context(256, 64);
    let setup = make_test_cpu_setup(1 << 13, 3, 8);
    let host = GpuGKRSetupHost::precompute_from_cpu_setup(&setup, 1, 0, 4, &context).unwrap();
    assert!(host.base_commitment_geometry().is_none());
    for k in [0, 2] {
        let config = ProverConfig::whir_only(
            13,
            WhirSchedule::from_legacy_arrays(2, 16, k, &[0, 5], &[1, 1], &[2], &[0, 0]),
            SecurityLevel::Sec100,
        );
        let geometry = BaseCommitmentGeometry::from_config(
            &config,
            BaseColumns {
                memory: 5,
                witness: 9,
                setup: 3,
            },
        )
        .unwrap();
        let constructed = std::cell::Cell::new(false);
        let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            host.validate_for_geometry(&geometry);
            constructed.set(true);
        }))
        .unwrap_err();
        let message = error
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| error.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(
            message.contains("legacy setup cannot supply packed, virtual or merged commitments")
        );
        assert!(!constructed.get());
    }
}

#[test]
fn legacy_setup_host_rejects_merged_identity_before_device_holder() {
    let context = make_test_context(256, 64);
    let setup = make_test_cpu_setup(1 << 13, 3, 8);
    let host = GpuGKRSetupHost::precompute_from_cpu_setup(&setup, 1, 1, 4, &context).unwrap();
    let mut config = ProverConfig::whir_only(
        13,
        WhirSchedule::from_legacy_arrays(2, 16, 0, &[1, 5], &[1, 1], &[2], &[0, 0]),
        SecurityLevel::Sec100,
    );
    config.commitment_mode = prover::gkr::prover_config::CommitmentMode::MergedMemoryAndWitness;
    let geometry = BaseCommitmentGeometry::from_config(
        &config,
        BaseColumns {
            memory: 5,
            witness: 9,
            setup: 3,
        },
    )
    .unwrap();
    let constructed = std::cell::Cell::new(false);
    let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        host.validate_for_geometry(&geometry);
        constructed.set(true);
    }))
    .unwrap_err();
    let message = error
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| error.downcast_ref::<&str>().copied())
        .unwrap();
    assert!(message.contains("legacy setup cannot supply packed, virtual or merged commitments"));
    assert!(!constructed.get());
}

#[test]
fn packed_base_cpu_parity_setup_host_transfer_and_logical_binding() {
    setup_host_transfer_and_logical_binding(1, &[0, 1, 2, 3, 4]);
}

#[test]
fn virtual_base_cpu_parity_setup_host_transfer_and_logical_binding() {
    setup_host_transfer_and_logical_binding(0, &[0, 2]);
}

fn setup_host_transfer_and_logical_binding(fold: usize, pack_logs: &[usize]) {
    let context = make_test_context(256, 64);
    let worker = Worker::new_with_num_threads(4);
    let baseline = context.get_used_mem_current();
    for &k in pack_logs {
        let mut config = ProverConfig::whir_only(
            13,
            WhirSchedule::from_legacy_arrays(2, 16, 0, &[fold, 5], &[1, 1], &[2], &[0, 0]),
            SecurityLevel::Sec100,
        );
        config.trace_len_log2 -= k;
        config.whir_schedule.base_round.physical_packing_log2 = k;
        let trace_len = 1usize << config.trace_len_log2;
        for columns in [1, (1usize << k) + 1] {
            let setup = make_test_cpu_setup(trace_len, columns, trace_len);
            let geometry = BaseCommitmentGeometry::from_config(
                &config,
                BaseColumns {
                    memory: 0,
                    witness: 0,
                    setup: columns,
                },
            )
            .unwrap();
            let twiddles = fft::Twiddles::<BF, Global>::new(1usize << 13, &worker);
            let inputs: Vec<&[BF]> = setup
                .hypercube_evals
                .iter()
                .map(|column| &column[..])
                .collect();
            let cpu = commit_trace_part_with_packing::<BF, E4, DefaultTreeConstructor, _>(
                &NaiveBackend,
                &inputs,
                &twiddles,
                2,
                fold,
                16,
                config.trace_len_log2,
                k,
                &GenericAllocationPool::proxy(),
                &worker,
            );
            let host = Arc::new(
                GpuGKRSetupHost::precompute_for_geometry(&setup, geometry, &context).unwrap(),
            );
            assert_eq!(host.unified_tree_cap(), cpu.get_cap().cap);
            assert_eq!(
                (host.log_domain_size as usize, host.columns_count),
                (config.trace_len_log2, columns)
            );
            assert_eq!(host.base_commitment_geometry(), Some(geometry));
            let mut transfer = GpuGKRSetupTransfer::new(host, &context).unwrap();
            let h2d = gpu_prover_context::transfer::single_shot_h2d(
                |t| transfer.schedule_transfer(t, &context),
                &context,
            )
            .unwrap();
            context.get_h2d_stream().synchronize().unwrap();
            let holder = &transfer.trace_holder;
            assert_eq!(
                (holder.log_domain_size as usize, holder.columns_count),
                (config.trace_len_log2, columns)
            );
            assert_eq!(holder.commitment_log_domain_size(), 13);
            assert_eq!(
                holder.committed_columns_count(),
                columns.div_ceil(1usize << k)
            );
            let mut padded = vec![BF::ZERO; holder.padded_hypercube_evals().len()];
            memory_copy_async(
                &mut padded,
                holder.padded_hypercube_evals(),
                context.get_exec_stream(),
            )
            .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            assert_eq!(&padded[..columns * trace_len], flatten_setup(&setup));
            assert!(padded[columns * trace_len..]
                .iter()
                .all(|value| *value == BF::ZERO));
            let mut storage = GpuGKRStorage::<BF, E4>::default();
            transfer.bind_setup_columns_into_storage(&mut storage);
            let first = storage.get_base_layer(GKRAddress::Setup(0)).clone_shared();
            for column in 0..columns {
                let poly = storage.get_base_layer(GKRAddress::Setup(column));
                assert_eq!((poly.offset(), poly.len()), (column * trace_len, trace_len));
                assert!(poly.shares_backing_with(&first));
            }
            drop(first);
            drop(storage);
            transfer.trace_holder.defer_materialization_until_queries(
                gpu_trace::trace::holder::OpeningStrategy::AllCosets,
            );
            transfer.trace_holder.finish_raw_batching(&context).unwrap();
            transfer
                .trace_holder
                .prepare_full_opening(&context)
                .unwrap();
            let slots = 1usize << fold;
            let indexes_host = [0u32, 1, 127, (1u32 << (13 - fold)) - 1, 0];
            let mut indexes = context
                .alloc(indexes_host.len(), AllocationPlacement::BestFit)
                .unwrap();
            memory_copy_async(&mut indexes, &indexes_host, context.get_exec_stream()).unwrap();
            for coset in 0..2 {
                let opened = transfer
                    .trace_holder
                    .get_leafs_and_merkle_paths(coset, &indexes, &context)
                    .unwrap();
                let leaves = opened.leafs.get_accessor();
                let paths = opened.merkle_paths.get_accessor();
                let mut output = Box::new(None);
                let dst = UnsafeMutAccessor::new(output.as_mut());
                let mut callbacks = Callbacks::new();
                callbacks
                    .schedule(
                        move || unsafe {
                            // SAFETY: these pool reads follow their D2H copies; output is
                            // consumed only after exec synchronization with callbacks alive.
                            assert!(dst
                                .get_mut()
                                .replace((leaves.get().to_vec(), paths.get().to_vec()))
                                .is_none());
                        },
                        context.get_exec_stream(),
                    )
                    .unwrap();
                drop(opened);
                context.get_exec_stream().synchronize().unwrap();
                drop(callbacks);
                let (leaves, paths) = output.unwrap();
                let physical = transfer.trace_holder.committed_columns_count();
                for (query, index) in indexes_host.iter().enumerate() {
                    let (_, _, expected) =
                        cpu.query_for_folded_index((*index as usize) * 2 + coset);
                    let actual_values: Vec<_> = (0..slots)
                        .flat_map(|slot| (0..physical).map(move |column| (column, slot)))
                        .map(|(column, slot)| {
                            leaves[column * indexes_host.len() * slots + query * slots + slot]
                        })
                        .collect();
                    assert_eq!(actual_values, expected.leaf_values_concatenated);
                    let actual_path: Vec<_> = (0..expected.path.len())
                        .map(|layer| paths[layer * indexes_host.len() + query])
                        .collect();
                    assert_eq!(actual_path, expected.path);
                }
            }
            drop(h2d);
            drop(indexes);
            drop(transfer);
            assert_eq!(context.get_used_mem_current(), baseline);
        }
    }
}
