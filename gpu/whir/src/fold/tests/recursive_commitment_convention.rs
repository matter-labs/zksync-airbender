//! Pins the RECURSIVE WHIR oracle's commitment convention: the same input
//! polynomial (natural-order multilinear monomial coefficients) is handed to the
//! live CPU recursive commit and to the current GPU `oracle_commit`, and the
//! produced commitment bytes (Merkle cap, every leaf's values, every leaf's
//! Merkle path) are compared. Both sides run production encoders — the CPU
//! reference is `Backend::lde_ext_poly_from_monomial_form` +
//! `commit_single_ext_poly` (through its `test-utils` shim) and, independently,
//! `CosetByCosetExtCommitment::commit`; neither side re-derives the encoding
//! here, so a shared convention mistake cannot self-confirm.

use std::alloc::Global;

use era_cudart::memory::memory_copy_async;
use fft::Twiddles;
use prover::gkr::prover::backend::{Backend, NaiveBackend};
use prover::gkr::whir::commit_single_ext_poly_for_test;
use prover::gkr::whir::coset_commit::CosetByCosetExtCommitment;
use prover::merkle_trees::{DefaultTreeConstructor, PathQueriable};
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
    // Production selector: coefficient leaves by default, eval leaves under the
    // feature. `commit_single_ext_poly` and `ext_coset_column` are gated on the
    // same feature, so the CPU references follow automatically.
    let transform_leaves_to_multilinear_coeffs = !cfg!(feature = "eval_leaves");
    let shape = format!(
        "log_trace_len={log_trace_len} lde_factor={lde_factor} \
         values_per_leaf={values_per_leaf} tree_cap_size={tree_cap_size}"
    );

    let worker = Worker::new();
    let context = make_test_context(512, 32);
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
        &worker,
    );
    let cpu = commit_single_ext_poly_for_test::<BF, E4, DefaultTreeConstructor>(
        rs,
        values_per_leaf,
        tree_cap_size,
        &worker,
    );

    let cpu_coset_by_coset = CosetByCosetExtCommitment::<BF, E4, DefaultTreeConstructor>::commit(
        &monomial_coeffs,
        &twiddles,
        lde_factor,
        values_per_leaf,
        tree_cap_size,
        &worker,
    );

    let mut gpu = GpuWhirExtensionOracle::from_monomial_coeffs(
        &monomial_coeffs,
        lde_factor,
        values_per_leaf,
        tree_cap_size,
        transform_leaves_to_multilinear_coeffs,
        &context,
    )
    .unwrap();

    let cpu_cap = PathQueriable::get_cap(&cpu.tree);
    assert_eq!(
        cpu_coset_by_coset.get_cap(),
        cpu_cap,
        "the two CPU recursive materializations disagree ({shape})",
    );
    assert_eq!(
        gpu.get_tree_cap(&context).unwrap(),
        cpu_cap,
        "recursive commitment cap: GPU vs live CPU ({shape})",
    );

    let total_leaves = trace_len * lde_factor / values_per_leaf;
    let mut tree_indexes = Vec::with_capacity(total_leaves);
    let mut expected_values = Vec::with_capacity(total_leaves);
    let mut expected_paths = Vec::with_capacity(total_leaves);
    for folded_index in 0..total_leaves {
        let (_, values, query) = cpu.query_for_folded_index(folded_index);
        tree_indexes.push(query.index as u32);
        expected_values.push(values);
        expected_paths.push(query.path);
    }
    let layers_count = expected_paths[0].len();
    assert!(expected_paths.iter().all(|path| path.len() == layers_count));

    let stream = context.get_exec_stream();
    let mut device_indexes = context
        .alloc::<u32>(total_leaves, AllocationPlacement::BestFit)
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

    for leaf_index in 0..total_leaves {
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
    // Shapes chosen to cross the GPU-side regime boundaries the recursive
    // oracle actually meets: values-per-leaf 2 and the production 32, the
    // full-tree and partial-tree cache modes, and small/mid forward-NTT
    // dispatch families.
    assert_recursive_commitment_matches_live_cpu(6, 4, 2, 4);
    assert_recursive_commitment_matches_live_cpu(10, 4, 32, 4);
    assert_recursive_commitment_matches_live_cpu(13, 4, 32, 4);
    assert_recursive_commitment_matches_live_cpu(10, 16, 32, 16);
}
