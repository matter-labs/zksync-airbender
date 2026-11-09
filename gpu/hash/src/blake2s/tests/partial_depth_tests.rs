use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

use super::super::{
    build_partial_merkle_tree_multi_coset_physical, gather_merkle_paths_from_rows_physical,
    gather_merkle_paths_partial_for_queries_physical,
    gather_merkle_paths_partial_for_queries_single_coset_physical, Digest, OraclePartialPathDesc,
    MAX_PARTIAL_TREE_REDUCTION_LAYERS, STATE_SIZE,
};
use super::physical_leaf_tests::{bitreverse_rows, random_values, upload};
use super::physical_query_gather_tests::{download, host_tower, upload_u32};
use super::random_digest;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::LOG_WARP_SIZE;

const SHAPES: [(u32, u32, usize, u32); 4] =
    [(11, 0, 2, 1), (12, 1, 1, 1), (12, 0, 4, 0), (13, 2, 2, 0)];
const COLS_COUNTS: [usize; 3] = [1, 3, 17];
const FEEDER_CASE: ((u32, u32, usize, u32), usize) = ((12, 1, 2, 1), 104);

fn cases() -> impl Iterator<Item = ((u32, u32, usize, u32), usize)> {
    SHAPES
        .into_iter()
        .flat_map(|shape| COLS_COUNTS.into_iter().map(move |cols| (shape, cols)))
        .chain(std::iter::once(FEEDER_CASE))
}

struct Oracle {
    natural: Vec<BF>,
    physical: DeviceAllocation<BF>,
    rows_count: usize,
    leaves_count: usize,
    log_leaves_count: u32,
    cols_count: usize,
    cosets_count: usize,
    log_rows_per_hash: u32,
}

impl Oracle {
    fn new(
        log_rows_per_coset: u32,
        log_rows_per_hash: u32,
        cosets_count: usize,
        cols_count: usize,
        stream: &CudaStream,
    ) -> Self {
        let rows_count = 1usize << log_rows_per_coset;
        let log_leaves_count = log_rows_per_coset - log_rows_per_hash;
        let natural = random_values(cols_count * rows_count * cosets_count);
        let physical = bitreverse_rows(&natural, cosets_count, cols_count, log_rows_per_coset);
        Self {
            physical: upload(&physical, stream),
            natural,
            rows_count,
            leaves_count: 1 << log_leaves_count,
            log_leaves_count,
            cols_count,
            cosets_count,
            log_rows_per_hash,
        }
    }

    fn values_len(&self) -> usize {
        self.natural.len()
    }

    fn coset_values_len(&self) -> usize {
        self.cols_count * self.rows_count
    }

    fn tower(&self, coset: usize) -> Vec<Vec<Digest>> {
        host_tower(
            &self.natural,
            coset * self.coset_values_len(),
            self.rows_count,
            self.cols_count,
            self.leaves_count,
            self.log_rows_per_hash,
            self.log_leaves_count,
        )
    }

    fn tree_stride(&self, reduction_layers: u32) -> usize {
        1 << (self.log_leaves_count + 1 - reduction_layers)
    }

    fn build_tree(
        &self,
        values: &DeviceAllocation<BF>,
        values_len: usize,
        cosets_count: usize,
        reduction_layers: u32,
        log_coset_cap: u32,
        stream: &CudaStream,
    ) -> (DeviceAllocation<Digest>, Vec<Digest>) {
        let tree_len = self.tree_stride(reduction_layers) * cosets_count;
        let sentinel = (0..tree_len).map(|_| random_digest()).collect::<Vec<_>>();
        let mut tree = DeviceAllocation::<Digest>::alloc(tree_len).unwrap();
        memory_copy_async(&mut tree, &sentinel, stream).unwrap();
        let mut scratch = (reduction_layers != LOG_WARP_SIZE).then(|| {
            DeviceAllocation::<Digest>::alloc(self.leaves_count >> LOG_WARP_SIZE).unwrap()
        });
        build_partial_merkle_tree_multi_coset_physical(
            &values[..values_len],
            &mut tree,
            self.log_rows_per_hash,
            self.log_leaves_count + 1 - reduction_layers - log_coset_cap,
            cosets_count,
            reduction_layers,
            scratch.as_deref_mut(),
            stream,
        )
        .unwrap();
        (tree, sentinel)
    }
}

fn subtree_boundary_queries(
    log_lde_factor: u32,
    log_leaves_count: u32,
    reduction_layers: u32,
) -> Vec<u32> {
    let leaves = 1u32 << log_leaves_count;
    let subtree = 1u32 << reduction_layers;
    let cosets = 1u32 << log_lde_factor;
    let mut internals = (0..leaves / subtree)
        .flat_map(|k| [k * subtree, k * subtree + subtree - 1])
        .chain([1, (leaves >> 1) + 1, leaves - 2])
        .collect::<Vec<_>>();
    internals.sort_unstable();
    internals.dedup();
    let mut queries = Vec::new();
    for coset in 0..cosets {
        for &internal in &internals {
            queries.push((internal << log_lde_factor) | coset);
        }
    }
    queries.push(queries[3]);
    queries.push(((leaves - 1) << log_lde_factor) | (cosets - 1));
    queries
}

fn assert_tree_matches_host(
    oracle: &Oracle,
    tree: &[Digest],
    reduction_layers: u32,
    log_coset_cap: u32,
    sentinel_check: &[Digest],
    label: &str,
) {
    let stride = oracle.tree_stride(reduction_layers);
    let cap_size = 1usize << log_coset_cap;
    for coset in 0..oracle.cosets_count {
        let tower = oracle.tower(coset);
        let mut expected = Vec::new();
        for layer in reduction_layers..=oracle.log_leaves_count - log_coset_cap {
            expected.extend_from_slice(&tower[layer as usize]);
        }
        assert_eq!(expected.len(), stride - cap_size, "{label}: layout");
        let slab = &tree[coset * stride..(coset + 1) * stride];
        for (i, (actual, wanted)) in slab.iter().zip(expected.iter()).enumerate() {
            assert_eq!(actual, wanted, "{label}: coset {coset} node {i}");
        }
        assert_eq!(
            &slab[stride - cap_size..],
            &sentinel_check[coset * stride + stride - cap_size..(coset + 1) * stride],
            "{label}: coset {coset} unused suffix was written"
        );
    }
}

fn expected_path(tower: &[Vec<Digest>], leaf: usize, layers_count: u32) -> Vec<Digest> {
    (0..layers_count as usize)
        .map(|layer| tower[layer][(leaf >> layer) ^ 1])
        .collect()
}

#[test]
fn partial_tree_depths_match_host_tree() {
    let stream = CudaStream::default();
    for ((log_rows_per_coset, log_rows_per_hash, cosets_count, log_coset_cap), cols_count) in
        cases()
    {
        let oracle = Oracle::new(
            log_rows_per_coset,
            log_rows_per_hash,
            cosets_count,
            cols_count,
            &stream,
        );
        for reduction_layers in LOG_WARP_SIZE..=MAX_PARTIAL_TREE_REDUCTION_LAYERS {
            let label = format!(
                "n={log_rows_per_coset} b={log_rows_per_hash} cosets={cosets_count} \
                     cap=2^{log_coset_cap} cols={cols_count} L={reduction_layers}"
            );
            let (tree, sentinel) = oracle.build_tree(
                &oracle.physical,
                oracle.values_len(),
                cosets_count,
                reduction_layers,
                log_coset_cap,
                &stream,
            );
            let host = download(&tree, &stream);
            stream.synchronize().unwrap();
            assert_tree_matches_host(
                &oracle,
                &host,
                reduction_layers,
                log_coset_cap,
                &sentinel,
                &label,
            );
        }
    }
}

#[test]
fn partial_path_gathers_match_host_paths_at_every_depth() {
    let stream = CudaStream::default();
    for ((log_rows_per_coset, log_rows_per_hash, cosets_count, log_coset_cap), cols_count) in
        cases()
    {
        let oracle = Oracle::new(
            log_rows_per_coset,
            log_rows_per_hash,
            cosets_count,
            cols_count,
            &stream,
        );
        let log_lde_factor = cosets_count.trailing_zeros();
        let layers_count = oracle.log_leaves_count - log_coset_cap;
        let towers = (0..cosets_count)
            .map(|c| oracle.tower(c))
            .collect::<Vec<_>>();
        for reduction_layers in LOG_WARP_SIZE..=MAX_PARTIAL_TREE_REDUCTION_LAYERS {
            let label = format!(
                "n={log_rows_per_coset} b={log_rows_per_hash} cosets={cosets_count} \
                     cap=2^{log_coset_cap} cols={cols_count} L={reduction_layers}"
            );
            let queries =
                subtree_boundary_queries(log_lde_factor, oracle.log_leaves_count, reduction_layers);
            let queries_device = upload_u32(&queries, &stream);
            let path_words = queries.len() * layers_count as usize * STATE_SIZE;
            let (tree, _) = oracle.build_tree(
                &oracle.physical,
                oracle.values_len(),
                cosets_count,
                reduction_layers,
                log_coset_cap,
                &stream,
            );

            let mut multi = upload_u32(&vec![0xa5a5a5a5; path_words], &stream);
            gather_merkle_paths_partial_for_queries_physical(
                OraclePartialPathDesc {
                    cosets_ptr: oracle.physical.as_ptr() as u64,
                    partial_tree_ptr: tree.as_ptr() as u64,
                    columns_count: cols_count as u32,
                    _pad: 0,
                    slab_dst_ptr: multi.as_mut_ptr() as u64,
                },
                log_lde_factor,
                log_rows_per_hash,
                oracle.log_leaves_count,
                layers_count,
                reduction_layers,
                &queries_device,
                &stream,
            )
            .unwrap();

            let lde_mask = cosets_count as u32 - 1;
            let expected_paths = queries
                .iter()
                .map(|&q| {
                    let coset = (q & lde_mask) as usize;
                    let leaf = (q >> log_lde_factor) as usize;
                    expected_path(&towers[coset], leaf, layers_count).concat()
                })
                .collect::<Vec<_>>();
            let multi_host = download(&multi, &stream);
            stream.synchronize().unwrap();
            assert_eq!(multi_host, expected_paths.concat(), "{label}: multi-coset");

            let mut expected_single = vec![0x5a5a5a5au32; path_words];
            let mut single = upload_u32(&expected_single, &stream);
            let coset_values_len = oracle.coset_values_len();
            let stride = oracle.tree_stride(reduction_layers);
            let path_len = layers_count as usize * STATE_SIZE;
            for coset in (0..cosets_count).rev() {
                gather_merkle_paths_partial_for_queries_single_coset_physical(
                    &oracle.physical[coset * coset_values_len..(coset + 1) * coset_values_len],
                    &tree[coset * stride..(coset + 1) * stride],
                    coset as u32,
                    log_lde_factor,
                    log_rows_per_coset,
                    log_rows_per_hash,
                    layers_count,
                    reduction_layers,
                    &queries_device,
                    &mut single,
                    &stream,
                )
                .unwrap();
                for (idx, &q) in queries.iter().enumerate() {
                    if (q & lde_mask) as usize == coset {
                        expected_single[idx * path_len..(idx + 1) * path_len]
                            .copy_from_slice(&expected_paths[idx]);
                    }
                }
                let single_host = download(&single, &stream);
                stream.synchronize().unwrap();
                assert_eq!(
                    single_host, expected_single,
                    "{label}: single-coset after coset {coset}"
                );
            }

            let coset = cosets_count - 1;
            let indexes = subtree_boundary_queries(0, oracle.log_leaves_count, reduction_layers);
            let indexes_device = upload_u32(&indexes, &stream);
            let mut rows_paths =
                DeviceAllocation::<Digest>::alloc(indexes.len() * layers_count as usize).unwrap();
            gather_merkle_paths_from_rows_physical(
                &indexes_device,
                false,
                &oracle.physical[coset * coset_values_len..(coset + 1) * coset_values_len],
                log_rows_per_hash,
                cols_count,
                &tree[coset * stride..(coset + 1) * stride],
                &mut rows_paths,
                layers_count,
                reduction_layers,
                &stream,
            )
            .unwrap();
            let rows_host = download(&rows_paths, &stream);
            stream.synchronize().unwrap();
            for (idx, &index) in indexes.iter().enumerate() {
                let expected = expected_path(&towers[coset], index as usize, layers_count);
                for (layer, digest) in expected.iter().enumerate() {
                    assert_eq!(
                        &rows_host[layer * indexes.len() + idx],
                        digest,
                        "{label}: rows index {idx} ({index}) layer {layer}"
                    );
                }
            }
        }
    }
}

#[test]
fn partial_path_gathers_accept_empty_queries() {
    let stream = CudaStream::default();
    let oracle = Oracle::new(12, 1, 2, 3, &stream);
    let empty_queries = DeviceAllocation::<u32>::alloc(1).unwrap();
    let mut empty_paths = DeviceAllocation::<u32>::alloc(8).unwrap();
    let mut empty_digests = DeviceAllocation::<Digest>::alloc(1).unwrap();
    for reduction_layers in [LOG_WARP_SIZE, MAX_PARTIAL_TREE_REDUCTION_LAYERS] {
        let layers_count = oracle.log_leaves_count;
        let (tree, _) = oracle.build_tree(
            &oracle.physical,
            oracle.values_len(),
            2,
            reduction_layers,
            0,
            &stream,
        );
        let stride = oracle.tree_stride(reduction_layers);
        let coset_values_len = oracle.coset_values_len();
        gather_merkle_paths_partial_for_queries_physical(
            OraclePartialPathDesc {
                cosets_ptr: oracle.physical.as_ptr() as u64,
                partial_tree_ptr: tree.as_ptr() as u64,
                columns_count: 3,
                _pad: 0,
                slab_dst_ptr: empty_paths.as_mut_ptr() as u64,
            },
            1,
            1,
            oracle.log_leaves_count,
            layers_count,
            reduction_layers,
            &empty_queries[..0],
            &stream,
        )
        .unwrap();
        gather_merkle_paths_partial_for_queries_single_coset_physical(
            &oracle.physical[..coset_values_len],
            &tree[..stride],
            0,
            1,
            12,
            1,
            layers_count,
            reduction_layers,
            &empty_queries[..0],
            &mut empty_paths[..0],
            &stream,
        )
        .unwrap();
        gather_merkle_paths_from_rows_physical(
            &empty_queries[..0],
            false,
            &oracle.physical[..coset_values_len],
            1,
            3,
            &tree[..stride],
            &mut empty_digests[..0],
            layers_count,
            reduction_layers,
            &stream,
        )
        .unwrap();
    }
    stream.synchronize().unwrap();
}
