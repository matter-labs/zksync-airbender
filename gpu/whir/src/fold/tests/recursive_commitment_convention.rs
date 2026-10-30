//! The recursive WHIR oracle's commitment convention against the live CPU commit:
//! neither side re-derives the encoding, so a shared mistake cannot self-confirm.

use std::alloc::Global;

use era_cudart::memory::memory_copy_async;
use fft::Twiddles;
use prover::allocation_pool::X86BabyBearAllocationPool;
use prover::gkr::prover::backend::{Backend, NaiveBackend};
use prover::gkr::whir::commit_single_ext_poly_for_test;
use prover::merkle_trees::{DefaultTreeConstructor, PathQueryable};
use worker::Worker;

use crate::test_utils::make_test_context;
use crate::{decode_leaf_values, GpuWhirExtensionOracle, EXT4_DEGREE};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::{BF, E4};

fn fixed_monomial_coeffs(trace_len: usize) -> Vec<E4> {
    let bf = |k: usize| {
        let mut x = (k as u32)
            .wrapping_mul(2654435761)
            .wrapping_add(0x9e37_79b9);
        x ^= x >> 15;
        BF::from_nonreduced_u32(x)
    };
    (0..trace_len)
        .map(|i| E4::from_array_of_base([bf(4 * i), bf(4 * i + 1), bf(4 * i + 2), bf(4 * i + 3)]))
        .collect()
}

fn assert_recursive_commitment_matches_live_cpu(
    log_trace_len: u32,
    lde_factor: usize,
    values_per_leaf: usize,
    tree_cap_size: usize,
) {
    let shape = format!(
        "log_trace_len={log_trace_len} lde_factor={lde_factor} \
         values_per_leaf={values_per_leaf} tree_cap_size={tree_cap_size}"
    );

    let worker = Worker::new();
    let context = make_test_context(if log_trace_len == 22 { 4096 } else { 512 }, 128);
    let baseline = context.get_used_mem_current();
    let trace_len = 1usize << log_trace_len;
    let monomial_coeffs = fixed_monomial_coeffs(trace_len);

    let backend = NaiveBackend;
    let twiddles: Twiddles<BF, Global> =
        <NaiveBackend as Backend<BF, E4>>::make_twiddles(&backend, trace_len, &worker);

    let rs = <NaiveBackend as Backend<BF, E4>>::lde_ext_poly_from_monomial_form(
        &backend,
        &monomial_coeffs,
        &twiddles,
        lde_factor,
        &X86BabyBearAllocationPool::new(),
        &worker,
    );
    let cpu = commit_single_ext_poly_for_test::<BF, E4, DefaultTreeConstructor>(
        rs,
        values_per_leaf,
        tree_cap_size,
        &worker,
    );

    {
        let depth = (trace_len * lde_factor / values_per_leaf / tree_cap_size).ilog2();
        let _range = gpu_core::primitives::nvtx::scoped_range(
            Some("ab"),
            match depth {
                5 => "g2.tree.depth5",
                6 => "g2.tree.depth6",
                _ => "g2.tree.other",
            },
        );
        let mut gpu = GpuWhirExtensionOracle::from_monomial_coeffs(
            &monomial_coeffs,
            lde_factor,
            values_per_leaf,
            tree_cap_size,
            &context,
        )
        .unwrap();

        if let crate::OracleValues::Recomputed(coefficients) = &gpu.values {
            assert_eq!(coefficients.len(), trace_len * EXT4_DEGREE);
            assert!(!gpu.trace_holder.are_cosets_materialized());
        }

        let cpu_cap = PathQueryable::get_cap(&cpu.tree);
        assert_eq!(
            gpu.get_tree_cap(&context).unwrap(),
            cpu_cap,
            "recursive commitment cap: GPU vs live CPU ({shape})",
        );

        let total_leaves = trace_len * lde_factor / values_per_leaf;
        // Preserve every old normal case's exhaustive count and the old
        // ignored large-domain edge sample. Larger new domains cannot fit
        // exhaustive paths into the helper's 128 MiB host pool.
        const MAX_EXHAUSTIVE_LEAVES: usize = 1 << 15;
        let folded_indexes: Vec<_> = if total_leaves > MAX_EXHAUSTIVE_LEAVES {
            let rows = trace_len / values_per_leaf;
            (0..lde_factor)
                .flat_map(|coset| {
                    [0, 1, rows / 2 - 1, rows / 2, rows - 1, 0]
                        .map(move |row| row * lde_factor + coset)
                })
                .collect()
        } else {
            (0..total_leaves).collect()
        };
        let queries_count = folded_indexes.len();
        assert!(queries_count > 0);
        let mut tree_indexes = Vec::with_capacity(queries_count);
        let mut expected_values = Vec::with_capacity(queries_count);
        let mut expected_paths = Vec::with_capacity(queries_count);
        for &folded_index in &folded_indexes {
            let (_, values, query) = cpu.query_for_folded_index(folded_index);
            tree_indexes.push(query.index as u32);
            expected_values.push(values);
            expected_paths.push(query.path);
        }
        let layers_count = expected_paths[0].len();
        assert!(expected_paths.iter().all(|path| path.len() == layers_count));

        let stream = context.get_exec_stream();
        let mut device_indexes = context
            .alloc::<u32>(queries_count, AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut device_indexes, &tree_indexes, stream).unwrap();
        let (host_leaves, host_paths) = gpu
            .schedule_query_outputs_to_host(&device_indexes, &context)
            .unwrap();
        let mut folded_indexes_device = context
            .alloc::<u32>(queries_count, AllocationPlacement::BestFit)
            .unwrap();
        let folded_indexes_u32: Vec<_> = folded_indexes
            .iter()
            .map(|&index| u32::try_from(index).unwrap())
            .collect();
        memory_copy_async(&mut folded_indexes_device, &folded_indexes_u32, stream).unwrap();
        let mut in_domain_reads = Vec::new();
        for _ in 0..2 {
            let mut leaves = context
                .alloc::<E4>(
                    queries_count * values_per_leaf,
                    AllocationPlacement::BestFit,
                )
                .unwrap();
            gpu.schedule_in_domain_leaves(&folded_indexes_device, &mut leaves, &context)
                .unwrap();
            // SAFETY: D2H writes every element before the post-sync reads below.
            let mut host = unsafe { context.alloc_host_uninit_slice(leaves.len()) };
            memory_copy_async(&mut host, &leaves, stream).unwrap();
            in_domain_reads.push(host);
        }
        // All readers are queued before retiring the coefficient oracle. Reuse
        // pool storage on exec before waiting for the test's terminal readback.
        drop(gpu);
        let mut recycled = context
            .alloc::<u8>(trace_len * size_of::<BF>(), AllocationPlacement::BestFit)
            .unwrap();
        era_cudart::memory::memory_set_async(&mut recycled, 0xa5, stream).unwrap();
        drop(recycled);
        stream.synchronize().unwrap();
        let host_leaves_accessor = host_leaves.get_accessor();
        let host_paths_accessor = host_paths.get_accessor();
        let host_leaves = unsafe { host_leaves_accessor.get() };
        let host_paths = unsafe { host_paths_accessor.get() };

        for leaf_index in 0..queries_count {
            let leaf_start = leaf_index * values_per_leaf * EXT4_DEGREE;
            let leaf_end = leaf_start + values_per_leaf * EXT4_DEGREE;
            assert_eq!(
                decode_leaf_values(&host_leaves[leaf_start..leaf_end], values_per_leaf),
                expected_values[leaf_index],
                "leaf {leaf_index} values: GPU vs live CPU ({shape})",
            );
            let path_start = leaf_index * layers_count;
            assert_eq!(
                &host_paths[path_start..path_start + layers_count],
                expected_paths[leaf_index].as_slice(),
                "leaf {leaf_index} Merkle path: GPU vs live CPU ({shape})",
            );
        }
        for read in &in_domain_reads {
            let accessor = read.get_accessor();
            // SAFETY: the test waited for every queued D2H above.
            let actual = unsafe { accessor.get() };
            for (index, expected) in expected_values.iter().enumerate() {
                assert_eq!(
                    &actual[index * values_per_leaf..(index + 1) * values_per_leaf],
                    expected,
                    "in-domain coefficient leaf {index}: GPU vs live CPU ({shape})",
                );
            }
        }
        eprintln!("recursive CPU parity: {shape}, queries={queries_count}, in_domain_reads=2, L2_bytes={}", context.get_device_properties().l2_cache_size_bytes);
    }
    assert_eq!(
        context.get_used_mem_current(),
        baseline,
        "recursive oracle reservations return to baseline"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn recursive_whir_commitment_matches_live_cpu() {
    // M256: compare every committed leaf and path against the CPU encoding.
    assert_recursive_commitment_matches_live_cpu(13, 4, 32, 4);
}

#[test]
#[cfg(not(no_cuda))]
fn recursive_whir_partial_tree_depth_five_matches_live_cpu() {
    // Exercise both commit dispatches with the reduction roots as the cap.
    // Each route also has a depth-six control with one upper tree level.
    assert_recursive_commitment_matches_live_cpu(9, 2, 16, 1);
    // Fused: 64 coefficient leaves, two-node cap, five path levels.
    assert_recursive_commitment_matches_live_cpu(9, 2, 16, 2);
    assert_recursive_commitment_matches_live_cpu(14, 2, 32, 16);
    // Retained: 1024 coefficient leaves, 32-node cap, five path levels.
    assert_recursive_commitment_matches_live_cpu(14, 2, 32, 32);
}

#[test]
#[cfg(not(no_cuda))]
fn recursive_whir_fused_shapes_match_live_cpu() {
    for (log_n, cosets, values, cap) in [
        (4, 256, 8, 4),
        (5, 64, 16, 1), // Four valid subtrees in an eight-subtree block.
        (6, 128, 32, 4),
        (7, 8, 16, 1), // M8 shuffle; two valid subtrees in the block.
        (8, 16, 16, 4),
        (9, 8, 16, 4),
        (10, 8, 32, 4),
        (11, 4, 32, 4),
        (12, 4, 32, 4),
        (13, 4, 32, 4),
    ] {
        assert_recursive_commitment_matches_live_cpu(log_n, cosets, values, cap);
    }
}

#[test]
#[cfg(not(no_cuda))]
fn recursive_whir_retained_shapes_match_live_cpu() {
    for log_n in 14..=19 {
        assert_recursive_commitment_matches_live_cpu(log_n, 2, 32, 16);
    }
}

#[test]
#[cfg(not(no_cuda))]
#[ignore = "full default virtual intermediate domain with independent CPU commitment"]
fn recursive_whir_retained_22_6_matches_live_cpu() {
    assert_recursive_commitment_matches_live_cpu(22, 32, 64, 16);
}

macro_rules! existing_recursive_route_cases {
    ($($name:ident: ($n:expr, $lde:expr, $values:expr, $cap:expr)),* $(,)?) => { $(
        #[test]
        #[cfg(not(no_cuda))]
        fn $name() {
            assert_recursive_commitment_matches_live_cpu($n, $lde, $values, $cap);
        }
    )* };
}
existing_recursive_route_cases! {
    recursive_whir_route_r1_subwarp_matches_live_cpu: (10, 64, 64, 16),
    recursive_whir_route_r2_block_matches_live_cpu: (10, 16, 16, 16),
    recursive_whir_route_r3_retained_matches_live_cpu: (14, 2, 16, 16),
    recursive_whir_route_r4_retained_matches_live_cpu: (14, 2, 32, 16),
    recursive_whir_subwarp_max_coefficients_match_live_cpu: (11, 2, 128, 1),
    recursive_whir_block_max_rows_min_slots_match_live_cpu: (10, 2, 4, 1),
    recursive_whir_retained_leaf9_matches_live_cpu: (14, 2, 512, 1),
    recursive_whir_retained_leaf13_matches_live_cpu: (18, 2, 8192, 1),
    recursive_whir_subwarp_horner_r2_matches_live_cpu: (5, 8, 8, 1),
    recursive_whir_subwarp_one_slot_matches_live_cpu: (2, 32, 1, 1),
    recursive_whir_subwarp_two_slots_match_live_cpu: (3, 8, 2, 1),
    recursive_whir_subwarp_constant_slots_match_live_cpu: (3, 32, 8, 1),
    recursive_whir_block_reader_ceiling_matches_live_cpu: (13, 2, 256, 1),
    recursive_whir_retained_tiled_residue19_matches_live_cpu: (20, 8, 2, 1),
    recursive_whir_retained_staging_residue20_matches_live_cpu: (21, 2, 2, 1),
}
