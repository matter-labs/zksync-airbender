use super::super::*;

use std::alloc::Global;

use crate::ops::powers::get_powers_by_val;
use era_cudart::memory::memory_copy_async;

use serial_test::serial;
use worker::Worker;

use crate::allocator::tracker::AllocationPlacement;
use crate::prover::test_utils::make_test_context;

use super::helpers::{
    copy_small_to_device, decode_base_leaf_values, query_base_trace_holder_for_folded_index,
};
use super::{copy_back_bf, make_lde_trace_holder};
use crate::upstream::{Blake2sU32MerkleTreeWithCap, ColumnMajorMerkleTreeConstructor, PrimeField};

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn base_query_paths_match_cpu_tree() {
    let context = make_test_context(256, 32);
    let worker = Worker::new();
    let columns: Vec<Vec<BF>> = vec![
        (0..8)
            .map(|i| BF::from_u32_unchecked(10 + i as u32))
            .collect(),
        (0..8)
            .map(|i| BF::from_u32_unchecked(30 + i as u32))
            .collect(),
    ];
    let log_lde_factor = 2u32;
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = 3u32;
    let rows = columns[0].len();
    let mut trace_holder = make_lde_trace_holder(
        &columns,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );

    let lde_factor = 1usize << log_lde_factor;
    let cosets_host = (0..lde_factor)
        .map(|coset_index| copy_back_bf(trace_holder.get_coset_evaluations(coset_index), &context))
        .collect::<Vec<_>>();
    let source_storage = cosets_host
        .iter()
        .map(|host| {
            (0..columns.len())
                .map(|column| {
                    let start = column * rows;
                    &host[start..start + rows]
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let source_refs = source_storage
        .iter()
        .map(|columns| columns.as_slice())
        .collect::<Vec<_>>();
    let cpu_tree = <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<
        BF,
    >>::construct_from_cosets::<BF, Global>(
        &source_refs,
        1usize << log_rows_per_leaf,
        1usize << log_tree_cap_size,
        true,
        true,
        false,
        &worker,
    );

    let total_queries = (rows << log_lde_factor) >> log_rows_per_leaf;
    for query_index in 0..total_queries {
        let (_, _, gpu_query) =
            query_base_trace_holder_for_folded_index(&mut trace_holder, query_index, &context)
                .unwrap();
        let (_, cpu_path) =
            <Blake2sU32MerkleTreeWithCap<Global> as ColumnMajorMerkleTreeConstructor<BF>>::get_proof::<Global>(
                &cpu_tree,
                query_index,
            );
        assert_eq!(gpu_query.path, cpu_path, "query_index={}", query_index);
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn base_query_leaf_and_path_helpers_match_combined_queries() {
    let context = make_test_context(256, 32);
    let columns: Vec<Vec<BF>> = vec![
        (0..8)
            .map(|i| BF::from_u32_unchecked(10 + i as u32))
            .collect(),
        (0..8)
            .map(|i| BF::from_u32_unchecked(30 + i as u32))
            .collect(),
    ];
    let log_lde_factor = 2u32;
    let log_rows_per_leaf = 1u32;
    let log_tree_cap_size = 3u32;
    let mut trace_holder = make_lde_trace_holder(
        &columns,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        &context,
    );
    let lde_factor = 1usize << log_lde_factor;
    let values_per_leaf = 1usize << log_rows_per_leaf;
    let coset_tree_size = (1usize << trace_holder.log_domain_size) / values_per_leaf;
    let total_queries = (columns[0].len() << log_lde_factor) >> log_rows_per_leaf;

    for query_index in [0usize, 1, 5, total_queries - 1] {
        let value_coset_index = query_index & (lde_factor - 1);
        let value_internal_index = query_index / lde_factor;
        let stage1_coset_index = query_index / coset_tree_size;
        let path_coset_index = super::bitreverse_index(stage1_coset_index, log_lde_factor);
        let path_internal_index = query_index % coset_tree_size;

        let mut value_index = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        let mut path_index = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        memory_copy_async(
            &mut value_index,
            &[value_internal_index as u32],
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut path_index,
            &[path_internal_index as u32],
            context.get_exec_stream(),
        )
        .unwrap();

        let combined_leafs = trace_holder
            .get_leafs_and_merkle_paths(value_coset_index, &value_index, &context)
            .unwrap()
            .leafs;
        let separate_leafs = trace_holder
            .get_query_leafs(value_coset_index, &value_index, &context)
            .unwrap();
        let combined_paths = trace_holder
            .get_leafs_and_merkle_paths(path_coset_index, &path_index, &context)
            .unwrap()
            .merkle_paths;
        let separate_paths = trace_holder
            .get_query_merkle_paths(path_coset_index, &path_index, &context)
            .unwrap();

        context.get_exec_stream().synchronize().unwrap();
        assert_eq!(
            unsafe { separate_leafs.get_accessor().get() },
            unsafe { combined_leafs.get_accessor().get() },
            "query {query_index} leaf helper diverged"
        );
        assert_eq!(
            unsafe { separate_paths.get_accessor().get() },
            unsafe { combined_paths.get_accessor().get() },
            "query {query_index} path helper diverged"
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn whir_build_eq_values_preserves_large_eval_buffer() {
    let context = make_test_context(2048, 32);
    let trace_len = 1usize << 24;
    let sample_len = 1024usize;
    let mid = trace_len / 2;
    let stream = context.get_exec_stream();

    let mut evals = context
        .alloc(trace_len, AllocationPlacement::BestFit)
        .unwrap();
    let fill = E4::from_array_of_base([BF::new(7), BF::new(13), BF::new(29), BF::new(43)]);
    get_powers_by_val(fill, 0, false, &mut evals, stream).unwrap();
    stream.synchronize().unwrap();

    let mut expected_head = vec![E4::ZERO; sample_len];
    let mut expected_mid = vec![E4::ZERO; sample_len];
    let mut expected_tail = vec![E4::ZERO; sample_len];
    memory_copy_async(&mut expected_head, &evals[..sample_len], stream).unwrap();
    memory_copy_async(&mut expected_mid, &evals[mid..mid + sample_len], stream).unwrap();
    memory_copy_async(
        &mut expected_tail,
        &evals[trace_len - sample_len..trace_len],
        stream,
    )
    .unwrap();
    stream.synchronize().unwrap();

    let mut point = context.alloc(24, AllocationPlacement::BestFit).unwrap();
    let coordinates = (0..24)
        .map(|idx| {
            E4::from_array_of_base([
                BF::new((idx + 3) as u32),
                BF::new((idx + 17) as u32),
                BF::new((idx + 31) as u32),
                BF::new((idx + 53) as u32),
            ])
        })
        .collect::<Vec<_>>();
    copy_small_to_device(&mut point, &coordinates, &context).unwrap();

    let mut eq = context
        .alloc(trace_len, AllocationPlacement::BestFit)
        .unwrap();
    let mut eq_group_tables = context
        .alloc(
            eq_group_tables_len(coordinates.len()).max(1),
            AllocationPlacement::BestFit,
        )
        .unwrap();
    launch_build_eq_values_from_point(
        point.as_ptr(),
        0,
        coordinates.len(),
        eq_group_tables.as_mut_ptr(),
        eq.as_mut_ptr(),
        trace_len,
        &context,
    )
    .unwrap();
    stream.synchronize().unwrap();

    let mut actual_head = vec![E4::ZERO; sample_len];
    let mut actual_mid = vec![E4::ZERO; sample_len];
    let mut actual_tail = vec![E4::ZERO; sample_len];
    memory_copy_async(&mut actual_head, &evals[..sample_len], stream).unwrap();
    memory_copy_async(&mut actual_mid, &evals[mid..mid + sample_len], stream).unwrap();
    memory_copy_async(
        &mut actual_tail,
        &evals[trace_len - sample_len..trace_len],
        stream,
    )
    .unwrap();
    stream.synchronize().unwrap();

    assert_eq!(actual_head, expected_head);
    assert_eq!(actual_mid, expected_mid);
    assert_eq!(actual_tail, expected_tail);
}

pub(crate) struct GpuScheduledBaseFieldQuery {
    pub(crate) index: usize,
    pub(crate) coset_index: usize,
    // Keeps index-fill callbacks alive until the stream executes them.
    #[allow(dead_code)]
    pub(super) callbacks: Callbacks<'static>,
    #[allow(dead_code)]
    pub(super) leafs: HostAllocation<[BF]>,
    #[allow(dead_code)]
    pub(super) merkle_paths: HostAllocation<[Digest]>,
    pub(super) values_per_leaf: usize,
    pub(super) columns_count: usize,
}

impl GpuScheduledBaseFieldQuery {
    pub(crate) fn decode(&self) -> (Vec<Vec<BF>>, BaseFieldQuery<BF, DefaultTreeConstructor>) {
        let leafs_accessor = self.leafs.get_accessor();
        let path_accessor = self.merkle_paths.get_accessor();
        let leafs = unsafe { leafs_accessor.get() };
        let path = unsafe { path_accessor.get().to_vec() };
        let decoded = decode_base_leaf_values(leafs, self.values_per_leaf, self.columns_count);
        let cpu_query = BaseFieldQuery {
            index: self.index,
            leaf_values_concatenated: decoded.iter().flatten().copied().collect(),
            path,
            _marker: PhantomData,
        };

        (decoded, cpu_query)
    }
}

pub(crate) fn clone_scheduled_whir_pre_pow_seeds(
    shared_state: UnsafeMutAccessor<ScheduledWhirProofState>,
) -> Vec<Seed> {
    unsafe { shared_state.get() }.pre_pow_seeds.clone()
}
