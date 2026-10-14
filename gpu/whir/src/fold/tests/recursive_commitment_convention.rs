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

/// Tree indexes of the first and last leaf under every cap node and in four
/// cosets, plus seeded interior leaves.
fn sampled_tree_indexes(
    total_leaves: usize,
    leaves_per_coset: usize,
    tree_cap_size: usize,
) -> Vec<usize> {
    let mut indexes = std::collections::BTreeSet::new();
    let leaves_per_cap_node = total_leaves / tree_cap_size;
    for node in 0..tree_cap_size {
        indexes.insert(node * leaves_per_cap_node);
        indexes.insert((node + 1) * leaves_per_cap_node - 1);
    }
    let cosets = total_leaves / leaves_per_coset;
    for coset in [0, 1, cosets / 2, cosets - 1] {
        indexes.insert(coset * leaves_per_coset);
        indexes.insert((coset + 1) * leaves_per_coset - 1);
    }
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..256 {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        indexes.insert((state >> 11) as usize % total_leaves);
    }
    indexes.into_iter().collect()
}

#[derive(Clone, Copy)]
enum Leaves {
    All,
    Sampled,
}

fn assert_recursive_commitment_matches_live_cpu(
    log_trace_len: u32,
    lde_factor: usize,
    values_per_leaf: usize,
    tree_cap_size: usize,
) {
    assert_recursive_commitment_leaves_match_live_cpu(
        log_trace_len,
        lde_factor,
        values_per_leaf,
        tree_cap_size,
        Leaves::All,
    );
}

fn assert_recursive_commitment_leaves_match_live_cpu(
    log_trace_len: u32,
    lde_factor: usize,
    values_per_leaf: usize,
    tree_cap_size: usize,
    leaves: Leaves,
) {
    let shape = format!(
        "log_trace_len={log_trace_len} lde_factor={lde_factor} \
         values_per_leaf={values_per_leaf} tree_cap_size={tree_cap_size}"
    );

    let worker = Worker::new();
    let context = match leaves {
        Leaves::All => make_test_context(512, 32),
        // Production codewords are 2 GiB of E4 values; the 30 GiB arena of the W4 gates.
        Leaves::Sampled => make_test_context(30 << 10, 256),
    };
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
    let folded_indexes: Vec<usize> = match leaves {
        Leaves::All => (0..total_leaves).collect(),
        Leaves::Sampled => {
            let leaves_per_coset = trace_len / values_per_leaf;
            let log_cosets = lde_factor.trailing_zeros();
            sampled_tree_indexes(total_leaves, leaves_per_coset, tree_cap_size)
                .into_iter()
                .map(|tree_index| {
                    let coset_dest = tree_index / leaves_per_coset;
                    let coset = if log_cosets == 0 {
                        0
                    } else {
                        coset_dest.reverse_bits() >> (usize::BITS - log_cosets)
                    };
                    (tree_index % leaves_per_coset) * lde_factor + coset
                })
                .collect()
        }
    };
    let queried_leaves = folded_indexes.len();
    let mut tree_indexes = Vec::with_capacity(queried_leaves);
    let mut expected_values = Vec::with_capacity(queried_leaves);
    let mut expected_paths = Vec::with_capacity(queried_leaves);
    for folded_index in folded_indexes {
        let (_, values, query) = cpu.query_for_folded_index(folded_index);
        tree_indexes.push(query.index as u32);
        expected_values.push(values);
        expected_paths.push(query.path);
    }
    if let Leaves::Sampled = leaves {
        let expected =
            sampled_tree_indexes(total_leaves, trace_len / values_per_leaf, tree_cap_size);
        assert!(tree_indexes
            .iter()
            .zip(&expected)
            .all(|(actual, expected)| *actual as usize == *expected));
    }
    let layers_count = expected_paths[0].len();
    assert!(expected_paths.iter().all(|path| path.len() == layers_count));

    let stream = context.get_exec_stream();
    let mut device_indexes = context
        .alloc::<u32>(queried_leaves, AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device_indexes, &tree_indexes, stream).unwrap();
    let (host_leaves, host_paths) = gpu
        .schedule_query_outputs_to_host(&device_indexes, &context)
        .unwrap();
    stream.synchronize().unwrap();
    let host_leaves_accessor = host_leaves.get_accessor();
    let host_paths_accessor = host_paths.get_accessor();
    let host_leaves = unsafe { host_leaves_accessor.get() };
    let host_paths = unsafe { host_paths_accessor.get() };

    for leaf_index in 0..queried_leaves {
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
}

#[test]
#[cfg(not(no_cuda))]
fn recursive_whir_commitment_matches_live_cpu() {
    // M256: compare every committed leaf and path against the CPU encoding.
    assert_recursive_commitment_matches_live_cpu(13, 4, 32, 4);
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
        // The 2^22 L1 feeder's fused oracles at its cap 32, with fewer cosets.
        (6, 256, 8, 32),
        (11, 32, 32, 32),
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
    for log_n in 15..=19 {
        assert_recursive_commitment_matches_live_cpu(log_n, 2, 32, 32);
    }
}

// The intermediate oracles of the 2^22 L1 feeder at the geometry its config
// produces: the full cap and sampled leaves and paths.
#[test]
#[cfg(not(no_cuda))]
fn l1_feeder_oracles_match_live_cpu() {
    let shapes = crate::test_utils::l1_feeder_oracle_shapes();
    assert!(!shapes.is_empty());
    for (log_n, log_v, lde_factor, cap_size) in shapes {
        assert_recursive_commitment_leaves_match_live_cpu(
            log_n,
            lde_factor,
            1 << log_v,
            cap_size,
            Leaves::Sampled,
        );
    }
}
