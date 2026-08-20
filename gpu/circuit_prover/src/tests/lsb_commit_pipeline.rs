//! Composed LSB commitment pipeline against the live CPU `commit_trace_part`.
//!
//! The GPU side runs the production entries back to back on a real
//! `TraceHolder`'s backings: hypercube evals -> monomials, natural monomials ->
//! bitreversed evals over the whole LDE, the physical Merkle builders, and the
//! physical query gathers. Nothing permutes rows between stages.

use super::*;

use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_hash::blake2s::{
    build_partial_merkle_tree_multi_coset_physical, gather_leaves_for_queries_physical,
    gather_merkle_paths_full_for_queries, gather_merkle_paths_partial_for_queries_physical,
    gather_tree_caps_inline, Digest, OracleGatherDesc, OraclePartialPathDesc, STATE_SIZE,
};
use gpu_ntt::ntt::{
    hypercube_evals_to_monomials, natural_monomials_to_bitreversed_evals_multi_coset,
};
use gpu_trace::trace::holder::{
    build_full_trees_from_physical, TraceHolder, TreesCacheMode, TreesHolder,
    PARTIAL_TREE_REDUCTION_LAYERS,
};
use prover::gkr::whir::ColumnMajorBaseOracleForLDE;

const DEVICE_ALLOCATOR_ARENA_BYTES: usize = 8usize << 30;
const HOST_POOL_SIZE_MB: usize = 256;
const DEVICE_ALLOCATOR_BLOCK_LOG_SIZE: u32 = 20;

#[derive(Clone, Copy, Debug)]
struct Shape {
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    log_lde_factor: u32,
    columns_count: usize,
}

impl Shape {
    fn rows(&self) -> usize {
        1usize << self.log_domain_size
    }

    fn cosets_count(&self) -> usize {
        1usize << self.log_lde_factor
    }

    fn values_per_leaf(&self) -> usize {
        1usize << self.log_rows_per_leaf
    }

    fn log_leaves_count(&self) -> u32 {
        self.log_domain_size - self.log_rows_per_leaf
    }

    /// Smallest cap the holder admits: `log_tree_cap_size >= log_lde_factor`,
    /// i.e. one digest per coset.
    fn log_tree_cap_size(&self) -> u32 {
        self.log_lde_factor
    }

    fn log_subtree_cap_size(&self) -> u32 {
        self.log_tree_cap_size() - self.log_lde_factor
    }

    fn path_layers_count(&self) -> u32 {
        self.log_leaves_count() - self.log_subtree_cap_size()
    }

    fn label(&self) -> String {
        format!(
            "n={} b={} lde=2^{} cols={}",
            self.log_domain_size, self.log_rows_per_leaf, self.log_lde_factor, self.columns_count,
        )
    }
}

fn bitreverse_index(index: usize, num_bits: u32) -> usize {
    if num_bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - num_bits)
    }
}

/// Boundary query indexes over the flat query domain
/// `q = (internal << log_lde_factor) | coset`: per coset the low and high edge
/// with their inward neighbours, both sides of a 32-leaf subtree boundary at
/// each end, and the coset midpoint pair. Element `0` is the global minimum
/// query, the last element the global maximum, and one query is repeated.
fn boundary_queries(log_lde_factor: u32, log_leaves_count: u32) -> Vec<u32> {
    assert!(log_leaves_count >= 6);
    let leaves = 1u32 << log_leaves_count;
    let cosets = 1u32 << log_lde_factor;
    let mut internals = vec![
        0,
        1,
        31,
        32,
        (leaves >> 1) - 1,
        leaves >> 1,
        leaves - 33,
        leaves - 32,
        leaves - 2,
        leaves - 1,
    ];
    internals.sort_unstable();
    internals.dedup();
    let mut queries = Vec::new();
    for coset in 0..cosets {
        for &internal in &internals {
            queries.push((internal << log_lde_factor) | coset);
        }
    }
    assert_eq!(queries[0], 0);
    queries.push(queries[3]);
    queries.push(((leaves - 1) << log_lde_factor) | (cosets - 1));
    queries
}

/// Column-major hypercube evaluations, `[col][row]`.
fn deterministic_hypercube_evals(shape: &Shape) -> Vec<BF> {
    let len = shape.columns_count * shape.rows();
    let mut out = Vec::with_capacity(len);
    let mut state: u32 = 0x9e37_79b9;
    for _ in 0..len {
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        out.push(BF::from_nonreduced_u32(state >> 1));
    }
    out
}

struct CpuReference {
    cap: Vec<Digest>,
    leaf_values: Vec<BF>,
    path_nodes: Vec<Digest>,
    /// Natural-order codeword of coset `k`, column `c`, at `k * cols + c`.
    coset_columns: Vec<Vec<BF>>,
}

/// The live prover commit path: `commit_trace_part` plus its query readers.
fn cpu_reference(shape: &Shape, hypercube_evals: &[BF], queries: &[u32]) -> CpuReference {
    let worker = Worker::new_with_num_threads(8);
    let rows = shape.rows();
    let twiddles: Twiddles<BF, Global> = Twiddles::new(rows, &worker);
    let inputs: Vec<&[BF]> = (0..shape.columns_count)
        .map(|col| &hypercube_evals[col * rows..(col + 1) * rows])
        .collect();
    let oracle = commit_trace_part::<BF, BF, DefaultTreeConstructor, _>(
        &NaiveBackend,
        &inputs,
        &twiddles,
        shape.cosets_count(),
        shape.log_rows_per_leaf as usize,
        1usize << shape.log_tree_cap_size(),
        shape.log_domain_size as usize,
        &worker,
    );
    let ColumnMajorBaseOracleForLDE::InMemory(in_memory) = oracle else {
        panic!("commit_trace_part returns the in-memory oracle");
    };

    let cap = in_memory.get_cap().cap;
    let mut leaf_values = Vec::new();
    let mut path_nodes = Vec::new();
    for &q in queries {
        let (_coset_index, values, query) = in_memory.query_for_folded_index(q as usize);
        leaf_values.extend(values.iter().flatten().copied());
        path_nodes.extend(query.path.iter().copied());
    }

    let mut coset_columns = Vec::with_capacity(shape.cosets_count() * shape.columns_count);
    for coset in in_memory.cosets.cosets.iter() {
        for column in coset.original_values_normal_order.iter() {
            coset_columns.push(column.column.to_vec());
        }
    }

    CpuReference {
        cap,
        leaf_values,
        path_nodes,
        coset_columns,
    }
}

struct GpuResult {
    cap: Vec<Digest>,
    leaf_values: Vec<BF>,
    path_nodes: Vec<Digest>,
    /// The materialized coset backing, `[coset][col][row]` in bitreversed row
    /// order.
    cosets: Vec<BF>,
}

fn gpu_commit_and_query(
    context: &ProverContext,
    shape: &Shape,
    hypercube_evals: &[BF],
    queries: &[u32],
    trees_cache_mode: TreesCacheMode,
) -> GpuResult {
    let stream = context.get_exec_stream();
    let device_properties = context.get_device_properties();
    let log_n = shape.log_domain_size;
    let rows = shape.rows();
    let cosets_count = shape.cosets_count();
    let columns_count = shape.columns_count;

    let mut holder = TraceHolder::<BF>::new(
        log_n,
        shape.log_lde_factor,
        shape.log_rows_per_leaf,
        shape.log_tree_cap_size(),
        columns_count,
        trees_cache_mode,
        context,
    )
    .unwrap();
    memory_copy_async(
        holder.get_uninit_hypercube_evals_mut(),
        hypercube_evals,
        stream,
    )
    .unwrap();

    let mut monomials = context
        .alloc::<BF>(columns_count * rows, AllocationPlacement::BestFit)
        .unwrap();
    {
        let source = DeviceMatrix::new(holder.get_hypercube_evals(), rows);
        let mut destination = DeviceMatrixMut::new(&mut monomials, rows);
        hypercube_evals_to_monomials(
            &source,
            &mut destination,
            log_n as usize,
            false,
            stream,
            device_properties,
        )
        .unwrap();
    }
    {
        let (cosets, trees) = holder.get_uninit_cosets_and_tree_mut();
        let source = DeviceMatrix::new(&monomials[..], rows);
        natural_monomials_to_bitreversed_evals_multi_coset(
            &source,
            &mut cosets[..],
            log_n as usize,
            shape.log_lde_factor as usize,
            columns_count,
            false,
            context.ntt_device_context(),
            None,
            stream,
            device_properties,
        )
        .unwrap();
        match trees {
            TreesHolder::Full(backing) => build_full_trees_from_physical(
                &cosets[..],
                &mut backing[..],
                log_n,
                shape.log_lde_factor,
                shape.log_rows_per_leaf,
                shape.log_tree_cap_size(),
                columns_count,
                cosets_count,
                stream,
            )
            .unwrap(),
            TreesHolder::Partial(backing) => {
                let layers_count = shape.log_leaves_count() + 1
                    - PARTIAL_TREE_REDUCTION_LAYERS
                    - shape.log_subtree_cap_size();
                build_partial_merkle_tree_multi_coset_physical(
                    &cosets[..],
                    &mut backing[..],
                    shape.log_rows_per_leaf,
                    layers_count,
                    cosets_count,
                    stream,
                )
                .unwrap()
            }
            TreesHolder::None => panic!("composed pipeline needs a cached tree"),
        }
    }
    holder.mark_cosets_materialized();

    let per_coset_segment_len = match trees_cache_mode {
        TreesCacheMode::CacheFull => 1usize << (shape.log_leaves_count() + 1),
        TreesCacheMode::CachePartial => {
            1usize << (shape.log_leaves_count() + 1 - PARTIAL_TREE_REDUCTION_LAYERS)
        }
        TreesCacheMode::CacheNone => unreachable!(),
    };
    let cap_size = 1usize << shape.log_tree_cap_size();
    let cap_words_per_coset = ((1usize << shape.log_subtree_cap_size()) * STATE_SIZE) as u32;
    let cap_offset_in_u32_words =
        (per_coset_segment_len - (1usize << (shape.log_subtree_cap_size() + 1))) * STATE_SIZE;
    let stride_in_u32_words = (per_coset_segment_len * STATE_SIZE) as u32;
    let tree_base_u32 = holder.get_consolidated_tree().unwrap().as_ptr() as *const u32;
    let mut device_cap: DeviceAllocation<Digest> = context
        .alloc(cap_size, AllocationPlacement::BestFit)
        .unwrap();
    {
        // SAFETY: `device_cap` owns `cap_size` digests; `Digest == [u32; 8]` so
        // the same bytes are a `cap_size * STATE_SIZE` u32 slice.
        let dst_u32 = unsafe {
            DeviceSlice::from_raw_parts_mut(
                device_cap.as_mut_ptr() as *mut u32,
                cap_size * STATE_SIZE,
            )
        };
        // SAFETY: the offset stays inside the first per-coset segment.
        let cap_base = unsafe { tree_base_u32.add(cap_offset_in_u32_words) };
        gather_tree_caps_inline(
            cap_base,
            cap_words_per_coset,
            stride_in_u32_words,
            shape.log_lde_factor,
            dst_u32,
            stream,
        )
        .unwrap();
    }
    holder.install_unified_device_cap(device_cap);
    let cap = holder.read_full_cap_synchronously(context).unwrap().cap;

    let queries_device = upload_slice_to_device_for_test(queries, context);
    let leaf_values_len = queries.len() * shape.values_per_leaf() * columns_count;
    let mut leaf_slab: DeviceAllocation<BF> = context
        .alloc(leaf_values_len, AllocationPlacement::BestFit)
        .unwrap();
    let path_layers_count = shape.path_layers_count();
    let path_nodes_len = queries.len() * path_layers_count as usize;
    let mut path_slab: DeviceAllocation<Digest> = context
        .alloc(path_nodes_len, AllocationPlacement::BestFit)
        .unwrap();

    let cosets_ptr = holder.get_consolidated_cosets().as_ptr() as u64;
    let tree_ptr = holder.get_consolidated_tree().unwrap().as_ptr() as u64;
    let mut leaf_descs = [OracleGatherDesc::default(); 3];
    leaf_descs[0] = OracleGatherDesc {
        cosets_ptr,
        columns_count: columns_count as u32,
        _pad: 0,
        slab_dst_ptr: leaf_slab.as_mut_ptr() as u64,
    };
    gather_leaves_for_queries_physical(
        &leaf_descs,
        1,
        shape.log_lde_factor,
        log_n,
        shape.log_rows_per_leaf,
        &queries_device,
        stream,
    )
    .unwrap();

    match trees_cache_mode {
        TreesCacheMode::CacheFull => {
            let tree = holder.get_consolidated_tree().unwrap();
            let stride_per_coset = tree.len() / cosets_count;
            // SAFETY: `path_slab` owns `path_nodes_len` digests; `Digest ==
            // [u32; 8]` so the same bytes are a `len * STATE_SIZE` u32 slice.
            let dst_u32 = unsafe {
                DeviceSlice::from_raw_parts_mut(
                    path_slab.as_mut_ptr() as *mut u32,
                    path_nodes_len * STATE_SIZE,
                )
            };
            gather_merkle_paths_full_for_queries(
                &queries_device,
                shape.log_lde_factor,
                stride_per_coset as u32,
                tree,
                dst_u32,
                path_layers_count,
                stream,
            )
            .unwrap();
        }
        TreesCacheMode::CachePartial => {
            let mut path_descs = [OraclePartialPathDesc::default(); 3];
            path_descs[0] = OraclePartialPathDesc {
                cosets_ptr,
                partial_tree_ptr: tree_ptr,
                columns_count: columns_count as u32,
                _pad: 0,
                slab_dst_ptr: path_slab.as_mut_ptr() as u64,
            };
            gather_merkle_paths_partial_for_queries_physical(
                &path_descs,
                1,
                shape.log_lde_factor,
                shape.log_rows_per_leaf,
                shape.log_leaves_count(),
                path_layers_count,
                &queries_device,
                stream,
            )
            .unwrap();
        }
        TreesCacheMode::CacheNone => unreachable!(),
    }

    let mut leaf_values = vec![BF::ZERO; leaf_values_len];
    let mut path_nodes = vec![Digest::default(); path_nodes_len];
    let mut cosets = vec![BF::ZERO; cosets_count * columns_count * rows];
    memory_copy_async(leaf_values.as_mut_slice(), &leaf_slab, stream).unwrap();
    memory_copy_async(path_nodes.as_mut_slice(), &path_slab, stream).unwrap();
    memory_copy_async(
        cosets.as_mut_slice(),
        holder.get_consolidated_cosets(),
        stream,
    )
    .unwrap();
    stream.synchronize().unwrap();

    GpuResult {
        cap,
        leaf_values,
        path_nodes,
        cosets,
    }
}

fn assert_elementwise_eq<T: Copy + PartialEq + std::fmt::Debug>(
    actual: &[T],
    expected: &[T],
    label: &str,
) {
    assert_eq!(actual.len(), expected.len(), "{label}: length");
    for (i, (a, e)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(a, e, "{label}: element {i}");
    }
}

fn assert_composed_pipeline_matches_cpu(shape: Shape) {
    let hypercube_evals = deterministic_hypercube_evals(&shape);
    let queries = boundary_queries(shape.log_lde_factor, shape.log_leaves_count());
    let cpu = cpu_reference(&shape, &hypercube_evals, &queries);

    let device_block_size = 1usize << DEVICE_ALLOCATOR_BLOCK_LOG_SIZE;
    let max_device_allocation_blocks_count = DEVICE_ALLOCATOR_ARENA_BYTES / device_block_size;
    let context = make_test_context_with_device_allocator_block_log_size(
        max_device_allocation_blocks_count,
        HOST_POOL_SIZE_MB,
        DEVICE_ALLOCATOR_BLOCK_LOG_SIZE,
    );

    for trees_cache_mode in [TreesCacheMode::CacheFull, TreesCacheMode::CachePartial] {
        let mode = match trees_cache_mode {
            TreesCacheMode::CacheFull => "full",
            TreesCacheMode::CachePartial => "partial",
            TreesCacheMode::CacheNone => unreachable!(),
        };
        let label = format!("{} tree={mode}", shape.label());
        let gpu = gpu_commit_and_query(
            &context,
            &shape,
            &hypercube_evals,
            &queries,
            trees_cache_mode,
        );

        // Stage boundary: the composed Mobius + natural->bitrev LDE is the CPU
        // codeword read in bitreversed row order.
        let rows = shape.rows();
        for coset in 0..shape.cosets_count() {
            for column in 0..shape.columns_count {
                let slab = coset * shape.columns_count + column;
                let expected = &cpu.coset_columns[slab];
                let actual = &gpu.cosets[slab * rows..(slab + 1) * rows];
                for row in 0..rows {
                    assert_eq!(
                        actual[row],
                        expected[bitreverse_index(row, shape.log_domain_size)],
                        "{label}: coset {coset} column {column} physical row {row}",
                    );
                }
            }
        }

        assert_elementwise_eq(&gpu.cap, &cpu.cap, &format!("{label}: cap"));
        assert_elementwise_eq(
            &gpu.leaf_values,
            &cpu.leaf_values,
            &format!("{label}: query leaf values"),
        );
        assert_elementwise_eq(
            &gpu.path_nodes,
            &cpu.path_nodes,
            &format!("{label}: merkle path nodes"),
        );
    }
}

#[test]
fn composed_lsb_commit_pipeline_matches_cpu_log21() {
    assert_composed_pipeline_matches_cpu(Shape {
        log_domain_size: 21,
        log_rows_per_leaf: 1,
        log_lde_factor: 1,
        columns_count: 1,
    });
}

#[test]
fn composed_lsb_commit_pipeline_matches_cpu_log20() {
    assert_composed_pipeline_matches_cpu(Shape {
        log_domain_size: 20,
        log_rows_per_leaf: 1,
        log_lde_factor: 1,
        columns_count: 1,
    });
}
